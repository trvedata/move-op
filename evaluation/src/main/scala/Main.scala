object Main extends App {
  def int(value: Int): generated.int = generated.int_of_integer(BigInt(value))

  val initState = (Nil, generated.hm_empty[String, (String, String)].apply(()))
  val operation = generated.Move((int(0), "a"), "parent", "meta", "child")
  val state = generated.example_apply_op(operation)(initState)
  println(state)
}
