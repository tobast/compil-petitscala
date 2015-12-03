class A {
  def f() { print("A.f\n") }
}

class B extends A {
  override def f()  { print("B.f\n") }
}

object Main { def main(args: Array[String]) {
  var a = new A();
  var b = new B();
  a.f();
  b.f();
  var x: A = b;
  x.f()
}
           }
