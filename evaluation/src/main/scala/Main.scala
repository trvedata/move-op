import java.util.Random

object Main extends App {
  val random = new Random()

  def operations(num: Int, actorId: BigInt) = {
    (0 to num).map { i =>
      val parent = BigInt(random.nextInt(1000))
      val child  = BigInt(random.nextInt(1000))
      generated.Move((BigInt(i), actorId), parent, "", child)
    }
  }

  var state: (List[generated.log_op[(BigInt, BigInt), BigInt, String]], generated.hashmap[BigInt, (String, BigInt)])
    = (Nil, generated.hm_empty[BigInt, (String, BigInt)].apply(()))

  println("applying local ops...")
  val start1 = System.nanoTime()
  for (op <- operations(1000, BigInt(1))) {
    state = generated.integer_apply_op(op)(state)
  }
  println("elapsed time: %d ms" format ((System.nanoTime() - start1) / 1000000))

  println("applying remote ops...")
  val start2 = System.nanoTime()
  for (op <- operations(1000, BigInt(2))) {
    state = generated.integer_apply_op(op)(state)
  }
  println("elapsed time: %d ms" format ((System.nanoTime() - start2) / 1000000))
}
