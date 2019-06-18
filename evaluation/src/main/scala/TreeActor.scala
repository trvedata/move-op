import akka.actor.{ Actor, Props }
import akka.event.Logging

object TreeActor {
  case class RequestMove(parent: String, metadata: String, child: String)

  def props(actorId: String) = Props(new TreeActor(actorId))
}

class TreeActor(actorId: String) extends Actor {
  val log = Logging(context.system, this)

  def int(value: Long): generated.int = generated.int_of_integer(BigInt(value))

  var state: (List[generated.log_op[(generated.int, String),String,String]], generated.hashmap[String,(String, String)])
    = (Nil, generated.hm_empty[String, (String, String)].apply(()))

  def receive = {
    case examplerpc.Move(timestamp, parent, metadata, child) => {
      val ts = (int(timestamp.get.counter), timestamp.get.replica)
      val operation = generated.Move(ts, parent, metadata, child)
      state = generated.example_apply_op(operation)(state)
      //log.info("Applied %s".format(operation))
      sender() ! timestamp.get
    }

    case TreeActor.RequestMove(parent, metadata, child) => ()
  }
}
