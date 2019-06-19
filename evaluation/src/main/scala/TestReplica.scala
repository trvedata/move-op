import akka.actor.{ ActorRef, ActorSystem }
import akka.grpc.GrpcClientSettings
import akka.http.scaladsl.UseHttp2.Always
import akka.http.scaladsl.model.{ HttpRequest, HttpResponse }
import akka.http.scaladsl.{ Http, HttpConnectionContext }
import akka.pattern.ask
import akka.stream.{ ActorMaterializer, Materializer }
import akka.util.Timeout
import com.codahale.metrics.{ ConsoleReporter, MetricRegistry, Meter, Timer }
import com.typesafe.config.ConfigFactory
import examplerpc.{ MoveService, MoveServiceClient, MoveServiceHandler }
import java.util.concurrent.TimeUnit.SECONDS
import java.util.Random
import scala.concurrent.{ ExecutionContext, Future }
import scala.concurrent.duration._
import scala.util.{ Failure, Success }

object TestReplica {

  // TCP port number for gRPC
  val PORT = 8080

  // Time interval between generated operations (= 1 / operation rate)
  val OPERATION_INTERVAL = 1000 millis

  def main(args: Array[String]): Unit = {
    if (args.length < 2) {
      throw new Exception("Usage: TestReplica own-ip remote-ip1 [remote-ip2 ...]")
    }

    val conf = ConfigFactory.parseString("akka.http.server.preview.enable-http2 = on")
      .withFallback(ConfigFactory.defaultApplication())

    implicit val metrics = new MetricRegistry()
    implicit val sys: ActorSystem = ActorSystem("TestReplica", conf)
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    ConsoleReporter.forRegistry(metrics).build().start(20, SECONDS)

    val treeActor = sys.actorOf(TreeActor.props(args(0), metrics), "treeActor")
    val service: HttpRequest => Future[HttpResponse] = MoveServiceHandler(new ReplicaService(treeActor, sys, metrics))

    val binding = Http().bindAndHandleAsync(service, interface = "0.0.0.0", port = PORT,
      connectionContext = HttpConnectionContext(http2 = Always))

    binding.foreach { binding =>
      println(s"gRPC server bound to: ${binding.localAddress}")
    }

    val generator = new LoadGenerator(treeActor, args.drop(1))
    generator.run()
    // ActorSystem threads will keep the app alive until `sys.terminate()` is called
  }
}

class LoadGenerator(treeActor: ActorRef, remoteReplicas: Array[String])
    (implicit val sys: ActorSystem, implicit val mat: Materializer,
     implicit val ec: ExecutionContext, implicit val metrics: MetricRegistry) {

  val random = new Random()

  val clients: Array[examplerpc.Move => Unit] = remoteReplicas.map { remoteIp =>
    val requests = metrics.timer(s"LoadGenerator($remoteIp).requests")
    val errors   = metrics.meter(s"LoadGenerator($remoteIp).errors")
    val config   = GrpcClientSettings.connectToServiceAt(remoteIp, TestReplica.PORT)
      .withDeadline(10 seconds)
      .withTls(false)
    sendRequest(remoteIp, MoveServiceClient(config), requests, errors)(_)
  }

  def sendRequest(remoteIp: String, client: MoveService, requests: Timer, errors: Meter)(operation: examplerpc.Move) {
    val timer = requests.time()
    client.sendMove(operation).onComplete {
      case Success(msg) =>
        timer.stop()
      case Failure(e) =>
        sys.log.info(s"Error in request to $remoteIp: $e")
        timer.stop()
        errors.mark()
    }
  }

  def generateOperation() {
    val parent  = "%d".format(random.nextInt(1000))
    val child   = "%d".format(random.nextInt(1000))
    val request = TreeActor.RequestMove(parent, "", child)
    implicit val timeout: Timeout = 3 seconds

    (treeActor ? request).mapTo[examplerpc.Move].onComplete {
      case Success(operation) =>
        for (client <- clients) client(operation)
      case Failure(e) =>
        sys.log.info(s"Error generating operation: $e")
    }
  }

  def run() {
    // Initially wait 20 seconds to allow all the replicas to boot up, then generate
    // operations in quick succession
    sys.scheduler.schedule(20 seconds, TestReplica.OPERATION_INTERVAL, () => generateOperation)
  }
}

class ReplicaService(treeActor: ActorRef, sys: ActorSystem, metrics: MetricRegistry) extends examplerpc.MoveService {
  val requests = metrics.timer("TestReplica.requests")

  override def sendMove(move: examplerpc.Move): Future[examplerpc.LamportTS] = {
    implicit val timeout: Timeout = 3 seconds
    import sys.dispatcher

    val timer = requests.time()
    try {
      (treeActor ? move).mapTo[examplerpc.LamportTS]
    } finally {
      timer.stop()
    }
  }
}
