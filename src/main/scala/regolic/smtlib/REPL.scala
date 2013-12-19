package regolic
package smtlib

class REPL(implicit val context: Context) {

  def run: Unit = {
    val stdinReader = new java.io.InputStreamReader(System.in)
    val parser = new Parser(stdinReader)
    Interpreter.execute(parser)
    //val interpreter = new Interpreter
    //while(true) {
    //  val cmd = parser.next
    //  val response = interpreter.eval(cmd)
    //  println(response)
    //}
    //throw new Exception("Should not happen")
  }
}
