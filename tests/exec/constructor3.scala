class A {
  var x = 1
}
class B extends A {
  var u = x = 2
}
object Main {
  def main(args: Array[String]) {
    var a = new A();
    print(a.x); print("\n");
    var b = new B();
    print(b.x); print("\n");
    var c: A = b;
    print(c.x); print("\n")
  }
}
