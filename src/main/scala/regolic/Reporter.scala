package regolic

object Reporter {

  private val errorPrefix   = "[ Error ] "
  private val warningPrefix = "[Warning] "
  private val infoPrefix    = "[ Info  ] "
  private val fatalPrefix   = "[ Fatal ] "
  private val debugPrefix   = "[ Debug ] "

  def output(msg: String) : Unit = {
    println(msg)
  }

  protected def reline(prefix: String, msg: String) : String = {
    val color = if(prefix == errorPrefix || prefix == warningPrefix || prefix == fatalPrefix) {
      Console.RED
    } else {
      Console.BLUE
    }
    "[" + color + prefix.substring(1, prefix.length-2) + Console.RESET + "] " +
    msg.trim.replaceAll("\n", "\n" + (" " * (prefix.size)))
  }

  def error(msg: Any) = output(reline(errorPrefix, msg.toString))
  def warning(msg: Any) = output(reline(warningPrefix, msg.toString))
  def info(msg: Any) = output(reline(infoPrefix, msg.toString))
  def fatalError(msg: Any) = { output(reline(fatalPrefix, msg.toString)); sys.exit(0) }
  def debug(msg: Any) = output(reline(debugPrefix, msg.toString))

}
