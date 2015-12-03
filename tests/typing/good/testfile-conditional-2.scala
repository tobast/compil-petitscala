
class A {}
class B extends A {}
class C { def foo(a: A, b: B) : A = if(true) a else b }
object Main { def main(args: Array[String]) { } }
