class A {
  var u = print("new A\n")
}
class B extends A {
  var v = print("new B\n")
}
object Main {
  def main(args: Array[String]) {
    var a = new A();
    var b = new B();
    var c: A = new B()
  }
}
