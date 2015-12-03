class Vehicle {
  var start = 10;
  var position = start;
  def move(d: Int) { position = position + d }
}

class Car extends Vehicle {
  var passengers = 0;

  def await(v: Vehicle) {
    if (v.position < position)
      v.move(position - v.position)
    else
      move(10)
  }
}

class Truck extends Vehicle {
  var load = 0;

  override def move(d: Int) {
    position = if (d <= 55) position + d else 55
  }
}

object Main {
  def main(args: Array[String]) {
    val t = new Truck();
    val c = new Car();
    c.passengers = 2;
    print(c.position); print("\n");
    c.move(60);
    print(c.position); print("\n");
    val v: Vehicle = c;
    v.move(70);
    print(c.position); print("\n");
    c.await(t);
    print(t.position); print("\n");
    print(c.position); print("\n")
  }
}

