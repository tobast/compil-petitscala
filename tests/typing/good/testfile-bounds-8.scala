
class U1 { def foo[B, C <: B, A >: C](a: A, b: B, c: C) { var x: B = c } }
object Main { def main(args: Array[String]) { } }
