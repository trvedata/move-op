import akka.actor.{ Actor, Props }
import akka.event.Logging
import com.codahale.metrics.MetricRegistry

object TreeActor {
  case class RequestMove(parent: Long, metadata: String, child: Long)

  def props(actorId: Long, metrics: MetricRegistry) = Props(new TreeActor(actorId, metrics))
}

class TreeActor(actorId: Long, metrics: MetricRegistry) extends Actor {
  val log = Logging(context.system, this)
  val localTimer  = metrics.timer("TreeActor.local")
  val remoteTimer = metrics.timer("TreeActor.remote")

  var counter: Long = 0

  var state: (List[generated.log_op[(BigInt, BigInt), BigInt, String]], generated.hashmap[BigInt, (String, BigInt)])
    = (Nil, generated.hm_empty[BigInt, (String, BigInt)].apply(()))

  def applyOp(op: examplerpc.Move) {
    val opCounter = op.timestamp.get.counter
    val timestamp = (BigInt(opCounter), BigInt(op.timestamp.get.replica))
    val operation = generated.Move(timestamp, BigInt(op.parent), op.metadata, BigInt(op.child))
    //log.info("Applied %s".format(operation))
    state = generated.integer_apply_op(operation)(state)
    if (opCounter > counter) counter = opCounter
  }

  def generateOp(parent: Long, metadata: String, child: Long): examplerpc.Move = {
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
