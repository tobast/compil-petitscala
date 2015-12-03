
class A { def m() {} }
class B[T <: A] { def foo(t: T) { t.m() } }
object Main { def main(args: Array[String]) { } }
