
class A[T](t: T) { var f: T = t }
class B(a: A[Int]) { var x = 42 + a.f }
object Main { def main(args: Array[String]) { } }
