class A {}
class B extends A { }
class M { def m() { var a: A = new B() } }
object Main { def main(args: Array[String]) { } }
