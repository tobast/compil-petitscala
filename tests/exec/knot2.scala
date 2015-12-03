
class Job[-A] { def work(x: A) {} }

class Knot extends Job[Int] {
  var j = new Job[Int]();
  var acc = 1;
  def knot() : Job[Int] = { j = this; j };
  override def work(x: Int) {
    if(x == 0) {
      print(acc);
      print("\n")
    } else {
      acc = acc * x;
      j.work(x-1)
    }
  }
}

object Main { def main(a: Array[String]) { (new Knot()).knot().work(10) } }

