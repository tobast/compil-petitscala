object Main {

  def main(args: Array[String]) {
    var i: Int = 0;
    var cpt: Int = 0;
    while (i < 10) {
      print(i);
      print(" ");
      var j: Int = 10;
      while (j > 0) {
	cpt = cpt+1;
	j = j-1
      };
      i = i+1
    };
    if (cpt == 100)
      print("\nok\n")
  }
}
