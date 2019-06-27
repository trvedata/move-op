import examplerpc.{ MoveService, MoveServiceClient }
import akka.actor.ActorSystem
import akka.grpc.GrpcClientSettings
import akka.stream.{ ActorMaterializer, Materializer }
import com.codahale.metrics.{ ConsoleReporter, MetricRegistry }
import java.util.concurrent.TimeUnit.SECONDS
import scala.concurrent.{ ExecutionContext, Future }
import scala.concurrent.duration._
import scala.util.{ Failure, Success }

object TestClient {

  val metrics  = new MetricRegistry()
  val requests = metrics.timer("TestClient.requests")
  val errors   = metrics.meter("TestClient.errors")

  def main(args: Array[String]): Unit = {
    implicit val sys: ActorSystem = ActorSystem("TestClient")
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    ConsoleReporter.forRegistry(metrics).build().start(20, SECONDS)

    val config = GrpcClientSettings.connectToServiceAt("18.138.235.108", 8080)
      .withDeadline(10 seconds)
      .withTls(false)
    val client: MoveService = MoveServiceClient(config)

    runSingleRequestReplyExample()

    sys.scheduler.schedule(10 millis, 10 millis) {
      runSingleRequestReplyExample()
    }

    def runSingleRequestReplyExample(): Unit = {
      val timer = requests.time()
      val timestamp = examplerpc.LamportTS(0, 1)
      val operation = examplerpc.Move(Some(timestamp), 0, "meta", 1)
      val reply = client.sendMove(operation)
      reply.onComplete {
        case Success(msg) =>
          timer.stop()
        case Failure(e) =>
          sys.log.info(s"Error response: $e")
          timer.stop()
          errors.mark()
      }
    }
  }
}
