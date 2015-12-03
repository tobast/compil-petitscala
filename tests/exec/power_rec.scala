class Power {
  def power(a: Int, n: Int) : Int = {
    if (n <= 0)
      return 1;
    var r = power(a, n / 2);
    r = r * r;
    if (n % 2 != 0)
      r = r * a;
    return r
  }
}

object Main { def main(args: Array[String]) {
  var p = new Power();
  print(p.power(2, 4)); print("\n");
  print(p.power(6, 3)); print("\n")
}
           }
