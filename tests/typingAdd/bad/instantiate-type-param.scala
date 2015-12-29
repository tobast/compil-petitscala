class UselessClass(a : Int) {
	val b = a+1
}
class T[A]() {
   def m() : A = {
	   new A()
   }
}
object Main {
    def main(args: Array[String]) {
		val tObj = new T[UselessClass]();
		val impossibleStuff = tObj.m()
    }
}
