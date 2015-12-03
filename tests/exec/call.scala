class A {
  var s : String = null;
  def set(x: String) { s = x };
  def get() : String = s
}

object Main {
  def main(args: Array[String]) {
    var a = new A();
    a.set("hello");
    print(a.get());
    print(", world!\n")
  }
}
