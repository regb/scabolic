package regolic
package smtlib

class REPL(implicit val context: Context) {

  def run: Nothing = {
    val stdinReader = new java.io.InputStreamReader(System.in)
    val interpreter = new Interpreter
    val parser = new Parser(stdinReader)
    while(true) {
      val cmd = parser.next
      val response = interpreter.eval(cmd)
      println(response)
    }
    throw new Exception("Should not happen")
  }
}
