class T[-A](a:A) {
   val b = a;
   def m() : Nothing = {
       val x : T[Nothing] = this;
       x.b
   }
}
class type_fail() {
   def magic[A, B] (a : A) : B = {
       val x = new T[A](a);
       x.m()
   }
}
object Main {
    val Obj = new type_fail();
    def main(args: Array[String]) {
        val x : Int = 0;
        val y : Boolean = Obj.magic[Int, Boolean](x)
    }
}
