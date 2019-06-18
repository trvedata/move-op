import akka.actor.ActorSystem
import akka.http.scaladsl.UseHttp2.Always
import akka.http.scaladsl.model.{ HttpRequest, HttpResponse }
import akka.http.scaladsl.{ Http, HttpConnectionContext }
import akka.pattern.ask
import akka.stream.{ ActorMaterializer, Materializer }
import akka.util.Timeout
import com.codahale.metrics.{ ConsoleReporter, MetricRegistry }
import com.typesafe.config.ConfigFactory
import examplerpc.MoveServiceHandler
import scala.concurrent.{ ExecutionContext, Future }
import scala.concurrent.duration._

object TestServer {
  val metrics = new MetricRegistry()

  def main(args: Array[String]): Unit = {
    ConsoleReporter.forRegistry(metrics).build().start(20, SECONDS)

    val conf = ConfigFactory.parseString("akka.http.server.preview.enable-http2 = on")
      .withFallback(ConfigFactory.defaultApplication())
    val system = ActorSystem("TestServer", conf)
    new TestServer(system, metrics).run()
    // ActorSystem threads will keep the app alive until `system.terminate()` is called
  }
}

class TestServer(system: ActorSystem, metrics: MetricRegistry) {

  def run(): Future[Http.ServerBinding] = {
    implicit val sys: ActorSystem = system
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    val service: HttpRequest => Future[HttpResponse] = MoveServiceHandler(new TestService(system, metrics))

    val binding = Http().bindAndHandleAsync(service, interface = "0.0.0.0", port = 8080,
      connectionContext = HttpConnectionContext(http2 = Always))

    binding.foreach { binding =>
      println(s"gRPC server bound to: ${binding.localAddress}")
    }

    binding
  }
}

class TestService(system: ActorSystem, metrics: MetricRegistry) extends examplerpc.MoveService {
  val requests  = metrics.timer("TestService.requests")
  val treeActor = system.actorOf(TreeActor.props("a"), "treeActor")

  override def sendMove(move: examplerpc.Move): Future[examplerpc.LamportTS] = {
    //println(s"received: ${move}")

    implicit val timeout: Timeout = 3 seconds
    import system.dispatcher

    val timer = requests.time()
    try {
      (treeActor ? move).mapTo[examplerpc.LamportTS]
    } finally {
      timer.stop()
    }
  }
}
