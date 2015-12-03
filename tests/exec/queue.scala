class List[+T](h: T, t: List[T]) {
  def head() : T = h;
  def tail() : List[T] = t
}

class Queue[+T](front: List[T], rear: List[T]) {

  def add[U >: T](x: U) : Queue[U] = new Queue[U](front, new List[U](x, rear));

  def rev_append[U](l1: List[U], l2: List[U]) : List[U] =
    if (l1 eq null) l2
    else rev_append[U](l1.tail(), new List[U](l1.head(), l2));

  def reverse[U](l: List[U]) : List[U] =
    rev_append[U](l, null);

  def head() : T =
    if (front ne null) front.head() else reverse[T](rear).head();

  def tail() : Queue[T] =
    if (front ne null) new Queue[T](front.tail(), rear)
    else new Queue[T](reverse[T](rear).tail(), null)

}

class Fruit {}
class Apple extends Fruit {}
class Pear  extends Fruit {}

object Main {
  def main(args: Array[String]) {
    var q: Queue[Int] = new Queue[Int](null, null);
    q = q.add[Int](1);
    q = q.add[Int](2);
    q = q.add[Int](3);
    print(q.head()); print("\n");
    q = q.tail();
    print(q.head()); print("\n");
    q = q.tail();
    print(q.head()); print("\n");

    var q1 = new Queue[Apple](null, null);
    val a: Apple = new Apple();
    q1 = q1.add[Apple](a);
    var q2 = q1.add[Fruit](new Pear());
    if (q2.head() eq a) print("OK\n")
  }
}
