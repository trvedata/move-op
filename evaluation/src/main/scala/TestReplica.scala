import akka.NotUsed
import akka.actor.{ ActorRef, ActorSystem }
import akka.grpc.GrpcClientSettings
import akka.http.scaladsl.UseHttp2.Always
import akka.http.scaladsl.model.{ HttpRequest, HttpResponse }
import akka.http.scaladsl.{ Http, HttpConnectionContext }
import akka.pattern.ask
import akka.stream.{ ActorMaterializer, Materializer }
import akka.stream.scaladsl.{ BroadcastHub, Keep, Sink, Source }
import akka.util.Timeout
import com.codahale.metrics.{ ConsoleReporter, MetricRegistry, Timer }
import com.typesafe.config.ConfigFactory
import examplerpc.{ MoveService, MoveServiceClient, MoveServiceHandler }
import java.util.concurrent.TimeUnit.SECONDS
import java.util.concurrent.ConcurrentHashMap
import java.util.Random
import scala.collection.JavaConversions._
import scala.concurrent.{ ExecutionContext, Future }
import scala.concurrent.duration._
import scala.util.{ Failure, Success }

object TestReplica {

  // TCP port number for gRPC
  val PORT = 8080

  // Time interval between generated operations (= 1 / operation rate)
  val OPERATION_INTERVAL = 1000 millis

  def main(args: Array[String]): Unit = {
    if (args.length < 1) {
      throw new Exception("Usage: TestReplica own-ip remote-ip1 [remote-ip2 ...]")
    }

    val conf = ConfigFactory.parseString("akka.http.server.preview.enable-http2 = on")
      .withFallback(ConfigFactory.defaultApplication())

    implicit val metrics = new MetricRegistry()
    implicit val sys: ActorSystem = ActorSystem("TestReplica", conf)
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    ConsoleReporter.forRegistry(metrics).build().start(20, SECONDS)

    val treeActor = sys.actorOf(TreeActor.props(args(0).toLong, metrics), "treeActor")
    val service: HttpRequest => Future[HttpResponse] = MoveServiceHandler(new ReplicaService(treeActor, sys, metrics))

    val binding = Http().bindAndHandleAsync(service, interface = "0.0.0.0", port = PORT,
      connectionContext = HttpConnectionContext(http2 = Always))

    binding.foreach { binding =>
      println(s"gRPC server bound to: ${binding.localAddress}")
    }

    val generator = new LoadGenerator(treeActor, args.drop(1))
    generator.run()

    sys.scheduler.scheduleOnce(10 minutes) {
      sys.terminate()
    }
  }
}

class LoadGenerator(treeActor: ActorRef, remoteReplicas: Array[String])
    (implicit val sys: ActorSystem, implicit val mat: Materializer,
     implicit val ec: ExecutionContext, implicit val metrics: MetricRegistry) {

  val random = new Random()
  val timers = new ConcurrentHashMap[String, Timer]()
  val requests = new ConcurrentHashMap[String, ConcurrentHashMap[examplerpc.LamportTS, Timer.Context]]()

  def run() {
    implicit val timeout: Timeout = 3 seconds

    val opStream: Source[examplerpc.Move, NotUsed] = Source
      // Initially wait 20 seconds to allow all the replicas to boot up, then generate
      // operations in quick succession
      .tick(20 seconds, TestReplica.OPERATION_INTERVAL, "tick")
      .map { _ => TreeActor.RequestMove(random.nextInt(1000), "", random.nextInt(1000)) }
      .mapAsync(1) { request => (treeActor ? request).mapTo[examplerpc.Move] }
      .mapMaterializedValue(_ => NotUsed)
      // Make the source multi-subscriber, broadcasting each item to all subscribers:
      // https://doc.akka.io/docs/akka/2.5.23/stream/stream-dynamic.html#using-the-broadcasthub
      .toMat(BroadcastHub.sink(bufferSize = 256))(Keep.right)
      .run()

    val responseStreams: Array[Pair[String, Source[examplerpc.LamportTS, NotUsed]]] = remoteReplicas.map { remoteIp =>
      timers.putIfAbsent(remoteIp, metrics.timer(s"LoadGenerator($remoteIp).requests"))
      requests.putIfAbsent(remoteIp, new ConcurrentHashMap[examplerpc.LamportTS, Timer.Context]())

      val requestStream = opStream.map { move =>
        val timer = timers.get(remoteIp).time()
        requests.get(remoteIp).putIfAbsent(move.timestamp.get, timer)
        move
      }

      val config = GrpcClientSettings.connectToServiceAt(remoteIp, TestReplica.PORT)
        .withDeadline(20 seconds)
        .withTls(false)

      (remoteIp, MoveServiceClient(config).sendMove(requestStream))
    }

    for ((remoteIp, responses) <- responseStreams) {
      responses.runForeach { response =>
        requests.get(remoteIp).remove(response).stop()
      }
    }
  }
}

class ReplicaService(treeActor: ActorRef, sys: ActorSystem, metrics: MetricRegistry) extends examplerpc.MoveService {
  override def sendMove(in: Source[examplerpc.Move, NotUsed]): Source[examplerpc.LamportTS, NotUsed] = {
    implicit val timeout: Timeout = 3 seconds
    import sys.dispatcher
    in.mapAsyncUnordered(10) { move => (treeActor ? move).mapTo[examplerpc.LamportTS] }
  }
}
