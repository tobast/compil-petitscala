class A {
    var x = 1;

    def f(x: Int) : Int = x;

    def g() : Int = { var x = 2; x }
}

object Main {
  def main(args: Array[String]) {
    var a = new A();
    print(a.x); print("\n");
    print(a.g()); print("\n");
    print(a.f(3)); print("\n")
  }
}
