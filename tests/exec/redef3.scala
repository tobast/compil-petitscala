class A {
  def f() : Boolean = true;
  def g() : Boolean = f()
}

class B extends A {
  override def f() : Boolean = false
}

object Main {

  def print_bool(b: Boolean) {
    print(if(b) "true" else "false");
    print("\n")
  };

  def main(args: Array[String]) {
    var a = new A();
    var b = new B();
    print_bool(a.f());
    print_bool(a.g());
    print_bool(b.f());
    print_bool(b.g());
    var x: A = b;
    print_bool(x.f());
    print_bool(x.g())
  }
}
