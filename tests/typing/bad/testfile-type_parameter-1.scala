class A { def m() {} }
class B[A] { def foo(a: A) { a.m() } }
object Main { def main(args: Array[String]) { } }
