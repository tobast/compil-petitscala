class Fact {
  def fact(n: Int) : Int = {
    var x = n;
    var res = 1;
    while (x > 1) {
      res = res * x;
      x = x-1
    };
    res
  }
}

object Main {
  def main(args: Array[String]) {
    var f = new Fact();
    print(f.fact(5)); print("\n");
    print(f.fact(11)); print("\n")
  }
}
