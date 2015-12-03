
class C[U, V >: U] {}
class Test { var x = new C[Int, Boolean]() }
object Main { def main(args: Array[String]) { } }
