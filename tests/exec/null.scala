class A { }

object Main {
  def main(args: Array[String]) {
    var a = new A();
    if (null ne null) print("oups\n");
    if (null ne a) print("yes!\n");
    if (null eq "toto") print("oups\n");
    a = null;
    if (a eq null) print("OK\n")
  }
}
