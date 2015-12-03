
class Omega { def omega() : Nothing = omega() }

class Function[-A,+B] extends Omega {
  def apply(x: A) : B = omega()
}

class State(s: String) extends Function[Int,Unit] {
  var f = new Function[Int,Unit]();
  def knot(g: Function[Int,Unit]) { f = g };
  override def apply(x: Int) : Unit = if(x == 0) print(s) else f.apply(x-1)
}

object Main {
  val even = new State("even\n");
  val odd = new State("odd\n");
  def knot() { even.knot(odd); odd.knot(even) };
  def main(a: Array[String]) {
    knot();
    var i = 42;
    while(i >= 0) { print(i); print(" "); even.apply(i); i = i - 1 }
  }
}

