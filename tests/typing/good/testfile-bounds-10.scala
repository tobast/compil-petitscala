
class C[+T] { def foo[A>:C[C[Boolean]]](a: C[Nothing]) : A = a }
object Main { def main(args: Array[String]) { } }
