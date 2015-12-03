class List(h: Int, n: List) {
  def length() : Int = 1 + (if (n eq null) 0 else n.length())
}

object Main {
  def main(args: Array[String]) {
    var l = new List(1, new List(2, new List(3, null)));
    print(l.length()); print("\n")
  }
}
