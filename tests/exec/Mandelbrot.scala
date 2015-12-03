

class Mandelbrot(steps: Int) {

  /* arithmetique de virgule fixe
   precision q = 8192 i.e. 13 bits pour la partie decimale */

  def add(x: Int, y: Int) : Int = {
    return x + y
  };
  def sub(x: Int, y: Int) : Int = {
    return x - y
  };
  def mul(x: Int, y: Int) : Int = {
    val t = x * y;
    return (t + 8192 / 2) / 8192
  };
  def div(x: Int, y: Int) : Int = {
    val t = x * 8192;
    return (t + y / 2) / y
  };
  def of_int(x: Int) : Int = {
    return x * 8192
  };

  def iter(n: Int, a: Int, b: Int, xn: Int, yn: Int) : Boolean = {
    if (n == 100) return true;
    val xn2 = mul(xn, xn);
    val yn2 = mul(yn, yn);
    if (add(xn2, yn2) > of_int(4)) return false;
    return iter(n+1, a, b, add(sub(xn2, yn2), a),
                add(mul(of_int(2), mul(xn, yn)), b))
  };

  def inside(x: Int, y: Int) : Boolean = {
    return iter(0, x, y, of_int(0), of_int(0))
  };

  def run() {
    val xmin = of_int(-2);
    val xmax = of_int(1);
    val deltax = div(sub(xmax, xmin), of_int(2 * steps));
    val ymin = of_int(-1);
    val ymax = of_int(1);
    val deltay = div(sub(ymax, ymin), of_int(steps));
    var i = 0;
    while (i < steps) {
      val y = add(ymin, mul(of_int(i), deltay));
      var j = 0;
      while (j < 2 * steps) {
        val x = add(xmin, mul(of_int(j), deltax));
        if (inside(x, y))
          print("0")
        else
          print("1");
        j = j+1
      };
      print("\n");
      i = i+1
    }

  }

}

object Main {
  def main(args: Array[String]) {
    new Mandelbrot(30).run()
  }
}
