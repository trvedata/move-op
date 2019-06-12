object Main extends App {
  val initState = (Nil, generated.hm_empty[String, (String, String)].apply(()))
  val operation = generated.Move((generated.zero_int, "a"), "parent", "meta", "child")
  val state = generated.example_apply_op(operation)(initState)
  println(state)
}
