class Power {
  def power(a: Int, n: Int) : Int = {
    var r = 1;
    var p = a;
    var e = n;
    while (e > 0) {
      if (e % 2 != 0) r = r * p;
      p = p * p;
      e = e / 2
    };
    r
   }
}

object Main {
  def main(args: Array[String]) {
    var p = new Power();
    print(p.power(2, 4)); print("\n");
    print(p.power(6, 3)); print("\n")
  }
}
