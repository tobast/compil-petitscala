class A { }

class B extends A {
    def g() { g(this,this) };
    def g(a: A, b: B) { };
    def g(b: B, a: A) { }
}
object Main { def main(args: Array[String]) { } }
