import akka.actor.ActorSystem
import akka.http.scaladsl.UseHttp2.Always
import akka.http.scaladsl.model.{ HttpRequest, HttpResponse }
import akka.http.scaladsl.{ Http, HttpConnectionContext }
import akka.stream.{ ActorMaterializer, Materializer }
import com.typesafe.config.ConfigFactory
import examplerpc.MoveServiceHandler
import scala.concurrent.{ ExecutionContext, Future }

object TestServer {

  def main(args: Array[String]): Unit = {
    val conf = ConfigFactory.parseString("akka.http.server.preview.enable-http2 = on")
      .withFallback(ConfigFactory.defaultApplication())
    val system = ActorSystem("TestServer", conf)
    new TestServer(system).run()
    // ActorSystem threads will keep the app alive until `system.terminate()` is called
  }
}

class TestServer(system: ActorSystem) {

  def run(): Future[Http.ServerBinding] = {
    implicit val sys: ActorSystem = system
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    val service: HttpRequest => Future[HttpResponse] = MoveServiceHandler(new TestService(system))

    val binding = Http().bindAndHandleAsync(service, interface = "0.0.0.0", port = 8080,
      connectionContext = HttpConnectionContext(http2 = Always))

    binding.foreach { binding =>
      println(s"gRPC server bound to: ${binding.localAddress}")
    }

    binding
  }
}
