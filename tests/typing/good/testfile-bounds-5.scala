
class U[B, C <: B, A >: C] { def foo(a: A, b: B, c: C) { var x: B = c } }
object Main { def main(args: Array[String]) { } }
