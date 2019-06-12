import java.util.Random

object Main extends App {
  def int(value: Int): generated.int = generated.int_of_integer(BigInt(value))

  var state: (List[generated.log_op[(generated.int, String),String,String]], generated.hashmap[String,(String, String)])
    = (Nil, generated.hm_empty[String, (String, String)].apply(()))
  val random = new Random()
  val startTime = System.nanoTime()

  for (i <- 1 to 1000) {
    val parent = "%d".format(random.nextInt(1000))
    val child  = "%d".format(random.nextInt(1000))
    val operation = generated.Move((int(i), "a"), parent, "", child)
    state = generated.example_apply_op(operation)(state)
  }

  println("elapsed time: %d ms" format ((System.nanoTime() - startTime) / 1000000))
}
