
class A[X] { def m(x: X) : X = x }
class B[X] extends A[X] { }
class C { var b = new B[Int](); var v = b.m(42) }
object Main { def main(args: Array[String]) { } }
