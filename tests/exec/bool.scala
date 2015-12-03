
object Main {
  def main(args: Array[String]) {
    var bool1 = true && false || true;   // true
    var bool2 = true && (false || true); // true
    var bool3 = true && ! true; // false
    var b = ! (bool1 && ! (bool2 || bool3)); // true
    if (b) print("OK\n")
  }
}
