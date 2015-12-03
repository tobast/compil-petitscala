
class A[T] { def m() : T = m() }
class B[T] extends A[T] { override def m() : T = m() }
object Main { def main(args: Array[String]) { } }
