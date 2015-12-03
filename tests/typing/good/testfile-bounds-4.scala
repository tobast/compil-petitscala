
class T[B, C <: B, A >: C] { def foo(a: A, b: B, c: C) { var x: A = c } }
object Main { def main(args: Array[String]) { } }
