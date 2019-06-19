import java.util.Random

object Main extends App {
  val random = new Random()

  def int(value: Int): generated.int = generated.int_of_integer(BigInt(value))

  def operations(num: Int, actorId: String) = {
    (0 to num).map { i =>
      val parent = "%d".format(random.nextInt(1000))
      val child  = "%d".format(random.nextInt(1000))
      generated.Move((int(i), actorId), parent, "", child)
    }
  }

  var state: (List[generated.log_op[(generated.int, String),String,String]], generated.hashmap[String,(String, String)])
    = (Nil, generated.hm_empty[String, (String, String)].apply(()))

  println("applying local ops...")
  val start1 = System.nanoTime()
  for (op <- operations(1000, "a")) {
    state = generated.example_apply_op(op)(state)
  }
  println("elapsed time: %d ms" format ((System.nanoTime() - start1) / 1000000))

  println("applying remote ops...")
  val start2 = System.nanoTime()
  for (op <- operations(1000, "b")) {
    state = generated.example_apply_op(op)(state)
  }
  println("elapsed time: %d ms" format ((System.nanoTime() - start2) / 1000000))
}
