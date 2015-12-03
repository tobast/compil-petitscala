
class Job { def work() {} }
class WriteString(s: String) extends Job { override def work() { print(s) } }
class WriteInt(x: Int) extends Job { override def work() { print(x) } }
class Sequenced(j1: Job,j2: Job) extends Job {
  override def work() { j1.work(); j2.work() }
}

class Writer extends Job {
  var output = new Job();
  var idt = 0;
  var nline = true;
  def app(j: Job) { output = new Sequenced(output,j) };
  def indent() {
    if(nline) {
      var m = idt;
      while(m > 0) { m = m - 1; app(new WriteString(" ")) };
      nline = false
    }
  };
  def append(j: Job) { indent(); app(j) };
  def prepend(j: Job) { output = new Sequenced(j,output) };
  def emit_string(s: String) { append(new WriteString(s)) };
  def emit_int(x: Int) { append(new WriteInt(x)) };
  def set_indent(x: Int) { idt = x };
  def move_indent(x: Int) { idt = idt + x };
  def newline() { emit_string("\n"); nline = true };
  def extract() : Job = { val u = output; output = new Job(); u };
  override def work() { output.work() }
}

class Quine extends Job {
  val mnw = new Writer();
  val mdw = new Writer();
  def n() { mdw.emit_string("n();"); mdw.newline() };
  def e(s: String) {
    mnw.emit_string(s);
    mdw.emit_string("e(\"");
    mdw.emit_string(s);
    mdw.emit_string("\"); ")
  };
  def en(s: String) {
    mnw.emit_string(s);
    mnw.newline();
    mdw.emit_string("en(\"");
    mdw.emit_string(s);
    mdw.emit_string("\"); ")
  };
  def s(s:String) {
    mnw.emit_string("\"");
    mnw.emit_string(s);
    mnw.emit_string("\"");
    mdw.emit_string("s(\"");
    mdw.emit_string(s);
    mdw.emit_string("\"); ")
  };
  def q() { mnw.emit_string("\""); mdw.emit_string("q(); ") };
  def sl() { mnw.emit_string("\\"); mdw.emit_string("sl(); ") };
  def swi(x: Int) {
    mdw.set_indent(x);
    mdw.emit_string("swi(");
    mdw.emit_int(x);
    mdw.emit_string("); ")
  };
  def si(x: Int) {
    mnw.set_indent(x);
    mdw.emit_string("si(");
    mdw.emit_int(x);
    mdw.emit_string("); ")
  };
  def mi(x: Int) {
    mnw.move_indent(x);
    mdw.emit_string("mi(");
    mdw.emit_int(x);
    mdw.emit_string("); ")
  };
  def li(x: Int) {
    mnw.move_indent(-x);
    mdw.emit_string("li(");
    mdw.emit_int(x);
    mdw.emit_string("); ")
  };
  def sw() { mdw.prepend(mnw.extract()); mdw.emit_string("sw(); ") };
  def t() {
    mdw.emit_string("t()");
    mdw.newline();
    mnw.prepend(mdw.extract());
    mnw.work()
  };
  override def work() {
    swi(4); si(0); en(""); en("class Job { def work() {} }"); n();
    e("class WriteString(s: String) extends Job "); n();
    en("{ override def work() { print(s) } }"); n();
    e("class WriteInt(x: Int) extends Job "); n();
    en("{ override def work() { print(x) } }"); n();
    en("class Sequenced(j1: Job,j2: Job) extends Job {"); mi(2); n();
    en("override def work() { j1.work(); j2.work() }"); li(2); n();
    en("}"); en(""); en("class Writer extends Job {"); mi(2); n();
    en("var output = new Job();"); en("var idt = 0;"); n();
    en("var nline = true;"); e("def app(j: Job) { "); n();
    en("output = new Sequenced(output,j) };"); n();
    en("def indent() {"); mi(2); n();
    en("if(nline) {"); mi(2); en("var m = idt;"); n();
    e("while(m > 0) { m = m - 1; app(new WriteString("); s(" "); n();
    en(")) };"); en("nline = false"); li(2); en("}"); li(2); en("};"); n();
    en("def append(j: Job) { indent(); app(j) };"); n();
    en("def prepend(j: Job) { output = new Sequenced(j,output) };"); n();
    en("def emit_string(s: String) { append(new WriteString(s)) };"); n();
    en("def emit_int(x: Int) { append(new WriteInt(x)) };"); n();
    en("def set_indent(x: Int) { idt = x };"); n();
    en("def move_indent(x: Int) { idt = idt + x };"); n();
    e("def newline() { emit_string("); q(); sl(); e("n"); q(); n();
    en("); nline = true };"); n();
    en("def extract() : Job = { val u = output; output = new Job(); u };"); n();
    en("override def work() { output.work() }"); li(2); en("}"); en(""); n();
    en("class Quine extends Job {"); mi(2); en("val mnw = new Writer();"); n();
    en("val mdw = new Writer();"); e("def n() { mdw.emit_string("); n();
    s("n();"); en("); mdw.newline() };"); en("def e(s: String) {"); mi(2); n();
    en("mnw.emit_string(s);"); e("mdw.emit_string("); q(); e("e("); sl(); n();
    s(""); en(");"); en("mdw.emit_string(s);"); e("mdw.emit_string("); n();
    q(); sl(); s("); "); en(")"); li(2); en("};"); n();
    en("def en(s: String) {"); mi(2); en("mnw.emit_string(s);"); n();
    en("mnw.newline();"); n();
    e("mdw.emit_string("); q(); e("en("); sl(); s(""); en(");"); n();
    en("mdw.emit_string(s);"); e("mdw.emit_string("); q(); sl(); s("); "); n();
    en(")"); li(2); en("};"); en("def s(s:String) {"); mi(2); n();
    e("mnw.emit_string("); q(); sl(); s(""); en(");"); n();
    en("mnw.emit_string(s);"); e("mnw.emit_string("); q(); sl(); s(""); n();
    en(");"); e("mdw.emit_string("); q(); e("s("); sl(); s(""); en(");"); n();
    en("mdw.emit_string(s);"); e("mdw.emit_string("); q(); sl(); s("); "); n();
    en(")"); li(2); en("};"); e("def q() { mnw.emit_string("); n();
    q(); sl(); s(""); e("); mdw.emit_string("); n();
    s("q(); "); en(") };"); e("def sl() { mnw.emit_string("); n();
    q(); sl(); sl(); q(); e("); mdw.emit_string("); s("sl(); "); n();
    en(") };"); en("def swi(x: Int) {"); mi(2); en("mdw.set_indent(x);"); n();
    e("mdw.emit_string("); s("swi("); en(");"); en("mdw.emit_int(x);"); n();
    e("mdw.emit_string("); s("); "); en(")"); li(2); en("};"); n();
    en("def si(x: Int) {"); mi(2); en("mnw.set_indent(x);"); n();
    e("mdw.emit_string("); s("si("); en(");"); en("mdw.emit_int(x);"); n();
    e("mdw.emit_string("); s("); "); en(")"); li(2); en("};"); n();
    en("def mi(x: Int) {"); mi(2); en("mnw.move_indent(x);"); n();
    e("mdw.emit_string("); s("mi("); en(");"); en("mdw.emit_int(x);"); n();
    e("mdw.emit_string("); s("); "); en(")"); li(2); en("};"); n();
    en("def li(x: Int) {"); mi(2); en("mnw.move_indent(-x);"); n();
    e("mdw.emit_string("); s("li("); en(");"); en("mdw.emit_int(x);"); n();
    e("mdw.emit_string("); s("); "); en(")"); li(2); en("};"); n();
    e("def sw() { mdw.prepend(mnw.extract()); mdw.emit_string("); n();
    s("sw(); "); en(") };"); en("def t() {"); mi(2); e("mdw.emit_string("); n();
    s("t()"); en(");"); en("mdw.newline();"); n();
    en("mnw.prepend(mdw.extract());"); en("mnw.work()"); li(2); en("};"); n();
    en("override def work() {"); sw(); en("}"); li(2); en("}"); n();
    en(""); e("object Main { def main(a: Array[String]) { "); n();
    en("(new Quine()).work() } }"); en(""); t()
  }
}

object Main { def main(a: Array[String]) { (new Quine()).work() } }

