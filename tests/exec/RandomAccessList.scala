
/* Random access lists (Okasaki, 1995)
 *
 * Un exemple utilisant de la récusion polymorphe
 */

class Pair[+A, +B](a: A, b: B) {
  val fst = a;
  val snd = b
}

class RandomAccessList[+E] {
  def length(): Int = length();
  def add[U >: E](x: U) : RandomAccessList[U] = add[U](x);
  def get(i: Int) : E = get(i)
}

// le booléen one indique si l'élément e est significatif
class Cons[E](one: Boolean, e: E, s: RandomAccessList[Pair[E, E]])
extends RandomAccessList[E] {

  override def length(): Int =
    2 * this.s.length() + (if (one) 1 else 0);

  override def get(i: Int) : E = {
    if (one) {
      if (i == 0) return this.e;
      var x: Pair[E, E] = this.s.get((i - 1) / 2);
      if (i % 2 == 1) x.fst else x.snd
    } else {
      var x: Pair[E, E] = this.s.get(i / 2);
      if (i % 2 == 0) x.fst else x.snd
    }
  };

  override def add[U >: E](x: U) : RandomAccessList[U] =
    if (one)
      new Cons[U](false, x, this.s.add[Pair[U,U]](new Pair[U,U](x, this.e)))
    else
      new Cons[U](true, x, s)

}

class Empty extends RandomAccessList[Nothing] {

  override def length(): Int = 0;

  override def get(i: Int) : Nothing = { print("no such element"); get(i) };

  override def add[E](x: E) : RandomAccessList[E] =
    new Cons[E](true, x, this)
}

object Main {
  def sequence(i: Int, j: Int) : RandomAccessList[Int] = {
    if (j < i)
      return new Empty()
    else
      return sequence(i + 1, j).add[Int](i)
  };
  def main(args: Array[String]) {
    val s: RandomAccessList[Int] = sequence(1, 10);
    var i = 0;
    while (i < 10) {
      print(s.get(i));
      print(" ");
      i = i+1
    };
    print("\n")
  }
}
