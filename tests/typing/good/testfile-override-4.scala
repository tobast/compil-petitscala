
class A { def m() : AnyVal = m() }
class B extends A { override def m() : Int = 42 }
object Main { def main(args: Array[String]) { } }
