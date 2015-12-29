class T[A]() extends A {
}
object Main {
    def main(args: Array[String]) {
		val tObj = new T[UselessClass]();
		val impossibleStuff = tObj.m()
    }
}
