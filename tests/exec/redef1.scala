class A {
  var a = 0;
  def set_a(a: Int) { this.a = a }
}

class B extends A {
  override def set_a(b: Int) { this.a = b * 2 }
}

object Main { def main(args: Array[String]) {
  var a = new A();
  var b = new B();
  a.set_a(1);
  b.set_a(1);
  print(a.a); print("\n");
  print(b.a); print("\n")
}
           }
