object Main {

  def print_bool(b: Boolean) {
    print(if(b) "true" else "false");
    print("\n")
  };

  def main(args: Array[String]) {
    print_bool(true);
    print_bool(false);
    print_bool(! true);
    print_bool(! false)
  }
}
