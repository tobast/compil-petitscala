object Main {

  var n = 999;
  var s = 0;

  def test() : Boolean = n % 3 == 0 || n % 5 == 0;

  def main(args: Array[String]) {
    if (n == 0) { print(s); print("\n") }
    else { if (test()) s = s + n; n = n - 1; main(args) }
  }
}
