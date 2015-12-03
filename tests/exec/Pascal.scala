
// triangle de Pascal modulo 7

class List(v: Int, n: List) {
  var value = v;
  var next = n;

  def get(i: Int) : Int = {
    if (i == 0) return value;
    return next.get(i-1)
  };

  def set(i: Int, v: Int) {
    if (i == 0) value = v
    else next.set(i-1, v)
  }

}

class Pascal(h: Int) {

  def print_row(r: List, i: Int) {
    var j = 0;
    while (j <= i) {
      if (r.get(j) != 0)
        print("*")
      else
        print("0");
      j = j+1
    };
    print("\n")
  };

  def compute_row(r: List, j: Int) {
    var v = 0;
    if (j == 0)
      v = 1
    else
      v = (r.get(j) + r.get(j-1)) % 7;
    r.set(j, v);
    if (j > 0)
      compute_row(r, j-1)
  };

  def create(n: Int) : List = {
    if (n == 0) return null;
    return new List(0, create(n-1))
  };

  def run() {
    val r = create(h+1);
    var i = 0;
    while (i < h) {
      r.set(i, 0);
      compute_row(r, i);
      print_row(r, i);
      i = i+1
    }
  }
}

object Main {
  def main(args: Array[String]) {
    new Pascal(42).run()
  }
}
