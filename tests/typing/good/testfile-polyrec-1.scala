class Pair[A,B] {}
class PolyRec { def foo[T](x:T) { foo[Pair[T,T]](new Pair[T,T]()) } }
object Main { def main(args: Array[String]) { } }
