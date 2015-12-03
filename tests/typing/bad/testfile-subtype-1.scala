class C[+T] { def foo[A>:C[Nothing]](a: C[C[Boolean]]) : A = a }
object Main { def main(args: Array[String]) { } }
