
object Main {
  def main(args: Array[String]) {
    var expr1 = - 7 + 6 * 5 - 4 / 3 - 2;     // 20
    var expr2 = (7 + 6) * (5 - 4) / 3 - 2; // 2
    var expr3 = 7 + 6 * (5 - 4 / (3 - 2));  // 13
    var sum = expr1 % 8 + expr2 + expr3;    // 19
    print(sum); print("\n")
  }
}
