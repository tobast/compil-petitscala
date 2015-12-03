object Main {
  def main(args: Array[String]) {
    if (false && 1/0==3) print("oups &&\n") else print("OK &&\n");
    if (true || 1/0==2) print("OK ||\n") else print("oups ||\n")
  }
}
