import examplerpc.{ MoveService, MoveServiceClient }
import akka.actor.ActorSystem
import akka.grpc.GrpcClientSettings
import akka.stream.{ ActorMaterializer, Materializer }
import scala.concurrent.{ ExecutionContext, Future }
import scala.concurrent.duration._
import scala.util.{ Failure, Success }

object TestClient {

  def main(args: Array[String]): Unit = {
    implicit val sys: ActorSystem = ActorSystem("TestClient")
    implicit val mat: Materializer = ActorMaterializer()
    implicit val ec: ExecutionContext = sys.dispatcher

    val config = GrpcClientSettings.connectToServiceAt("localhost", 8080)
      .withDeadline(1.second)
      .withTls(false)
    val client: MoveService = MoveServiceClient(config)

    runSingleRequestReplyExample()

    sys.scheduler.schedule(1.second, 1.second) {
      runSingleRequestReplyExample()
    }

    def runSingleRequestReplyExample(): Unit = {
      sys.log.info("Performing request")
      val timestamp = examplerpc.LamportTS(0, "a")
      val operation = examplerpc.Move(Some(timestamp), "parent", "meta", "child")
      val reply = client.sendMove(operation)
      reply.onComplete {
        case Success(msg) =>
          println(s"got single reply: $msg")
        case Failure(e) =>
          println(s"Error response: $e")
      }
    }
  }
}
