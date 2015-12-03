class A {}
class B extends A {}
class C extends B {}
class Test { var x: A = new C() }
object Main { def main(args: Array[String]) { } }
