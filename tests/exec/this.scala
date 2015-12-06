class A {
  var a = 0;
  def m() : A = { this.a = this.a + 1; print(this.a); print("\n"); return this }
}

object Main {
  def main(args: Array[String]) {
    var a = new A();
    var b = a.m();
    var c = b.m()
  }
}
