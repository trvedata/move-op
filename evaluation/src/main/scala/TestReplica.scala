import com.codahale.metrics.{ ConsoleReporter, MetricRegistry, Timer, Gauge }
import java.io.{ ByteArrayInputStream, ByteArrayOutputStream, DataInputStream, DataOutputStream, InputStream, OutputStream }
import java.net.{ ServerSocket, Socket }
import java.util.concurrent.{ArrayBlockingQueue, ConcurrentHashMap, TimeUnit}
import java.util.Random

object TestReplica {

  // TCP port number for communication between replicas
  val PORT = 8080

  // Time interval between generated operations (= 1 / operation rate)
  val OPERATION_INTERVAL = TimeUnit.MICROSECONDS.toNanos(1000000)

  // If false, runs in CRDT mode. If true, uses leader-based replication.
  val USE_LEADER = true

  // How long to run the test before shutting down
  val RUN_DURATION = TimeUnit.MINUTES.toNanos(10)

  // Backpressure kicks in if more than this number of requests in flight
  val MAX_PENDING_REQUESTS = if (USE_LEADER) 5000 else 50

  def startDaemon[T <: Runnable](runnable: T): T = {
    val thread = new Thread(runnable)
    thread.setDaemon(true)
    thread.start()
    return runnable
  }

  def main(args: Array[String]): Unit = {
    if (args.length < 1) {
      throw new Exception("Usage: TestReplica replica-id remote-ip1 [remote-ip2 ...]")
    }

    implicit val metrics = new MetricRegistry()
    ConsoleReporter.forRegistry(metrics).build().start(20, TimeUnit.SECONDS)

    val replicaId = args(0).toLong
    val replica = new ReplicaThread(replicaId, metrics)
    new Thread(replica).start()

    startDaemon(new AcceptThread(replica))

    TimeUnit.SECONDS.sleep(10) // time for other servers to come up

    if (USE_LEADER) {
      // Leader mode: connect to only one IP, namely the leader
      if (replicaId > 0) {
        replica.addClient(startDaemon(new FollowerThread(args(1), replica, metrics)))
      }
    } else {
      // CRDT mode: connect to all of the remote IPs
      for (remoteIp <- args.drop(1)) {
        replica.addClient(startDaemon(new CRDTClientThread(remoteIp, metrics)))
      }
    }
  }
}

// Encoding/decoding objects <--> bytes
object Protocol {
  case class Move(time: Long, replica: Long, parent: Long, child: Long)
  case class Ack(time: Long, replica: Long)

  def encodeMove(move: Move): Array[Byte] = {
    val bytes = new ByteArrayOutputStream(4 * 8)
    val data = new DataOutputStream(bytes)
    data.writeLong(move.time)
    data.writeLong(move.replica)
    data.writeLong(move.parent)
    data.writeLong(move.child)
    bytes.toByteArray()
  }

  def encodeAck(ack: Ack): Array[Byte] = {
    val bytes = new ByteArrayOutputStream(2 * 8)
    val data = new DataOutputStream(bytes)
    data.writeLong(ack.time)
    data.writeLong(ack.replica)
    bytes.toByteArray()
  }

  def decodeMove(bytes: Array[Byte]): Move = {
    val data = new DataInputStream(new ByteArrayInputStream(bytes))
    val time    = data.readLong()
    val replica = data.readLong()
    val parent  = data.readLong()
    val child   = data.readLong()
    Move(time, replica, parent, child)
  }

  def decodeAck(bytes: Array[Byte]): Ack = {
    val data = new DataInputStream(new ByteArrayInputStream(bytes))
    val time    = data.readLong()
    val replica = data.readLong()
    Ack(time, replica)
  }
}

// Base class for ClientThread and ServerThread. Assumes that each incoming
// message has a fixed size in bytes (given as recvFrameSize).
abstract class Connection(socket: Socket, recvFrameSize: Int) extends Runnable {
  socket.setTcpNoDelay(true)

  def send(bytes: Array[Byte]) {
    this.synchronized {
      socket.getOutputStream().write(bytes)
    }
  }

  // Called when a whole incoming message has been received
  def receive(bytes: Array[Byte])

  // The run loop blocks waiting for bytes to be received. It waits for a message
  // (recvFrameSize bytes) to be received and then calls receive().
  def run() {
    try {
      val recvBuf = new Array[Byte](recvFrameSize)
      val inputStream = socket.getInputStream()
      var bytesRead = 0
      while (true) {
        val ret = inputStream.read(recvBuf, bytesRead, recvFrameSize - bytesRead)
        if (ret <= 0) return
        bytesRead += ret
        if (bytesRead == recvFrameSize) {
          receive(recvBuf)
          bytesRead = 0
        }
      }
    } finally {
      println(s"Closing connection: ${this}")
      socket.close()
    }
  }
}

trait ClientThread {
  def send(move: Protocol.Move)
  def backpressure: Boolean
}

// Thread that handles the client side of a connection. It sends Move requests
// to the server, and waits for Ack responses in reply.
class CRDTClientThread(val remoteIp: String, metrics: MetricRegistry)
    extends Connection(new Socket(remoteIp, TestReplica.PORT), 2 * 8) with ClientThread {

  val timer = metrics.timer(s"ClientThread($remoteIp).requests")
  val requests = new ConcurrentHashMap[Protocol.Ack, Timer.Context]()

  def send(move: Protocol.Move) {
    val requestId = Protocol.Ack(move.time, move.replica)
    requests.putIfAbsent(requestId, timer.time())
    this.send(Protocol.encodeMove(move))
  }

  def receive(bytes: Array[Byte]) {
    val ack = Protocol.decodeAck(bytes)
    requests.remove(ack).stop()
  }

  // Returns false if we're happy to accept more requests, and true if we need
  // to hold off on enqueueing more requests for now.
  def backpressure: Boolean = {
    requests.size() >= TestReplica.MAX_PENDING_REQUESTS
  }
}

// Thread that handles the client side of a connection to a leader. It sends
// Move requests to the leader, and waits for Move responses in reply.
class FollowerThread(val leaderIp: String, replica: ReplicaThread, metrics: MetricRegistry)
    extends Connection(new Socket(leaderIp, TestReplica.PORT), 4 * 8) with ClientThread {

  val timer = metrics.timer(s"ClientThread($leaderIp).requests")
  val requests = new ConcurrentHashMap[Protocol.Ack, Timer.Context]()

  metrics.register("RequestsMapSize", new Gauge[Int] {
    def getValue: Int = requests.size
  })

  def send(move: Protocol.Move) {
    val requestId = Protocol.Ack(move.time, move.replica)
    requests.putIfAbsent(requestId, timer.time())
    this.send(Protocol.encodeMove(move))
  }

  def receive(bytes: Array[Byte]) {
    val move = Protocol.decodeMove(bytes)
    val requestId = Protocol.Ack(move.time, move.replica)
    val timer = requests.remove(requestId)
    if (timer != null) timer.stop()
    replica.request(move, null)
  }

  // Returns false if we're happy to accept more requests, and true if we need
  // to hold off on enqueueing more requests for now.
  def backpressure: Boolean = {
    requests.size() >= TestReplica.MAX_PENDING_REQUESTS
  }
}

// Thread that handles the server side of a connection. It waits for Move
// requests from a client, and gets the replica to process them. When done, it
// sends either an Ack response (in CRDT mode) or a Move response (in leader mode)
// back to the client.
class ServerThread(replica: ReplicaThread, socket: Socket) extends Connection(socket, 4 * 8) {
  replica.addServer(this)

  def send(ack: Protocol.Ack) {
    this.send(Protocol.encodeAck(ack))
  }

  def send(move: Protocol.Move) {
    this.send(Protocol.encodeMove(move))
  }

  def receive(bytes: Array[Byte]) {
    replica.request(Protocol.decodeMove(bytes), this)
  }
}

// Thread that accepts connections on a server socket, and spawns a new
// ServerThread for each incoming connection.
class AcceptThread(replica: ReplicaThread) extends Runnable {
  def run() {
    val server = new ServerSocket(TestReplica.PORT)
    while (true) {
      val socket = server.accept()
      println(s"Incoming connection: ${socket}")
      new Thread(new ServerThread(replica, socket)).start()
    }
  }
}

// This thread is the main execution loop of a replica. It manages the replica
// state and calls into the Isabelle-generated code to update the state.
class ReplicaThread(replicaId: Long, metrics: MetricRegistry) extends Runnable {
  val localTimer   = metrics.timer("ReplicaThread.local")
  val remoteTimer  = metrics.timer("ReplicaThread.remote")
  val backpressure = metrics.meter("ReplicaThread.backpressure")
  val queue = new ArrayBlockingQueue[Tuple2[Protocol.Move, ServerThread]](64)
  val random = new Random()

  var clients: List[ClientThread] = Nil
  var servers: List[ServerThread] = Nil

  // For Lamport timestamps
  var counter: Long = 0

  // The current state of the replica (consisting of both log and tree).
  // Type comes from generated code, hence horrible.
  var state: (List[generated.log_op[(BigInt, BigInt), BigInt, String]], generated.hashmap[BigInt, (String, BigInt)])
    = (Nil, generated.hm_empty[BigInt, (String, BigInt)].apply(()))

  def addClient(client: ClientThread) {
    clients = client :: clients
  }

  def addServer(server: ServerThread) {
    servers = server :: servers
  }

  // Incoming request from a ServerThread. The calling object is passed in so
  // that we know where to send the response once we've processed the operation.
  def request(move: Protocol.Move, sender: ServerThread) {
    queue.put((move, sender))
  }

  // Executes a remote operation. This is called on the replica thread.
  private[this] def processRequest(move: Protocol.Move, sender: ServerThread) {
    val timer = remoteTimer.time()
    try {
      //println(s"Received: ${move}")
      applyMove(move)
      if (TestReplica.USE_LEADER) {
        for (server <- servers) server.send(move) // Replicate to all followers
      } else {
        sender.send(Protocol.Ack(move.time, move.replica))
      }
    } finally {
      timer.stop()
    }
  }

  // Generates a new move operation.
  // In CRDT mode: applies it locally, and sends it to all of the clients.
  // In leader mode: does nothing if we are the leader (replicaId == 0),
  // otherwise generates a move operation and sends it to the leader.
  private[this] def generateMove() {
    if (TestReplica.USE_LEADER && replicaId == 0) return
    counter += 1
    val move = Protocol.Move(counter, replicaId, random.nextInt(1000), random.nextInt(1000))
    //println(s"Generated: ${move}")
    if (!TestReplica.USE_LEADER) {
      val timer = localTimer.time()
      try {
        this.applyMove(move)
      } finally {
        timer.stop()
      }
    }
    for (client <- clients) client.send(move)
  }

  // Actually applies a move operation to the current state (calls into
  // Isabelle-generated code). Both local and remote operations.
  private[this] def applyMove(move: Protocol.Move) {
    val timestamp = if (TestReplica.USE_LEADER) {
      counter += 1
      (BigInt(counter), BigInt(replicaId))
    } else {
      if (move.time > counter) counter = move.time
      (BigInt(move.time), BigInt(move.replica))
    }
    val operation = generated.Move(timestamp, BigInt(move.parent), "", BigInt(move.child))
    state = generated.integer_apply_op(operation)(state)

    // Truncate the log from time to time
    if (counter % 100000 == 0) {
      state = (state._1.take(1000), state._2)
    }
  }

  // The run loop does two things: it blocks waiting for incoming requests from
  // other replicas on the blocking queue, and it also generates a new operation
  // every REQUEST_INTERVAL (unless backpressure is applied).
  def run() {
    TimeUnit.SECONDS.sleep(20) // time for all replicas to start up
    val startTime = System.nanoTime()
    var nextTick = startTime + TestReplica.OPERATION_INTERVAL
    while (System.nanoTime() < startTime + TestReplica.RUN_DURATION) {
      val request = queue.poll(nextTick - System.nanoTime(), TimeUnit.NANOSECONDS)
      if (request == null) {
        if (clients.exists(_.backpressure)) {
          backpressure.mark()
        } else {
          generateMove()
        }
        nextTick += TestReplica.OPERATION_INTERVAL
      } else {
        processRequest(request._1, request._2)
      }
    }
  }
}
