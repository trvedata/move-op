import akka.actor.ActorSystem
import akka.pattern.ask
import akka.util.Timeout
import scala.concurrent.Future
import scala.concurrent.duration._

class TestService(system: ActorSystem) extends examplerpc.MoveService {

  val treeActor = system.actorOf(TreeActor.props("a"), "treeActor")

  override def sendMove(move: examplerpc.Move): Future[examplerpc.LamportTS] = {
    println(s"received: ${move}")

    implicit val timeout: Timeout = 3.seconds
    import system.dispatcher

    (treeActor ? move).mapTo[examplerpc.LamportTS]
  }
}
