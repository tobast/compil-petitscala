class Fact {
  def fact(n: Int) : Int = {
    if (n <= 1)
      1
    else
      n * fact(n-1)
  }
}

object Main {
  def main(args: Array[String]) {
    var f = new Fact();
    print(f.fact(5)); print("\n");
    print(f.fact(11)); print("\n")
  }
}
