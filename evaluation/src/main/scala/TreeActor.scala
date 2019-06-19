import akka.actor.{ Actor, Props }
import akka.event.Logging
import com.codahale.metrics.MetricRegistry

object TreeActor {
  case class RequestMove(parent: String, metadata: String, child: String)

  def props(actorId: String, metrics: MetricRegistry) = Props(new TreeActor(actorId, metrics))
}

class TreeActor(actorId: String, metrics: MetricRegistry) extends Actor {
  val log = Logging(context.system, this)
  val localTimer  = metrics.timer("TreeActor.local")
  val remoteTimer = metrics.timer("TreeActor.remote")

  var counter: Long = 0

  var state: (List[generated.log_op[(generated.int, String),String,String]], generated.hashmap[String,(String, String)])
    = (Nil, generated.hm_empty[String, (String, String)].apply(()))

  def int(value: Long): generated.int = generated.int_of_integer(BigInt(value))

  def applyOp(op: examplerpc.Move) {
    val opCounter = op.timestamp.get.counter
    val timestamp = (int(opCounter), op.timestamp.get.replica)
    val operation = generated.Move(timestamp, op.parent, op.metadata, op.child)
    //log.info("Applied %s".format(operation))
    state = generated.example_apply_op(operation)(state)
    if (opCounter > counter) counter = opCounter
  }

  def generateOp(parent: String, metadata: String, child: String): examplerpc.Move = {
    val timestamp = examplerpc.LamportTS(counter + 1, actorId)
    val operation = examplerpc.Move(Some(timestamp), parent, metadata, child)
    applyOp(operation)
    operation
  }

  def receive = {
    // Remote request
    case op: examplerpc.Move => {
      val timer = remoteTimer.time()
      try {
        applyOp(op)
        sender() ! op.timestamp.get
      } finally {
        timer.stop()
      }
    }

    // Local request
    case TreeActor.RequestMove(parent, metadata, child) => {
      val timer = localTimer.time()
      try {
        val operation = generateOp(parent, metadata, child)
        sender() ! operation
      } finally {
        timer.stop()
      }
    }
  }
}
