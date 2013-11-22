package regolic

object Logger {

  object LogLevel extends Enumeration {
    type Level = Value
    val Error = Value(0)
    val Warning = Value(1)
    val Info = Value(2)
    val Debug = Value(3)
    val Trace = Value(4)
  }

}

abstract class Logger {

  import Logger._

  private val errorPrefix   = "[ Error ] "
  private val warningPrefix = "[Warning] "
  private val infoPrefix    = "[ Info  ] "
  private val debugPrefix   = "[ Debug ] "
  private val tracePrefix   = "[ Trace ] "

  def output(msg: String): Unit

  val logLevel: LogLevel.Level

  protected def reline(prefix: String, msg: String): String = {
    val color = 
      if(prefix == errorPrefix) 
        Console.RED
      else if(prefix == warningPrefix) 
        Console.YELLOW
      else if(prefix == debugPrefix || prefix == tracePrefix)
        Console.MAGENTA
      else
        Console.BLUE
    "[" + color + prefix.substring(1, prefix.length-2) + Console.RESET + "] " +
    msg.trim.replaceAll("\n", "\n" + (" " * (prefix.size)))
  }

  def error(msg: Any) = if(logLevel >= LogLevel.Error) output(reline(errorPrefix, msg.toString))
  def warning(msg: Any) = if(logLevel >= LogLevel.Warning) output(reline(warningPrefix, msg.toString))
  def info(msg: Any) = if(logLevel >= LogLevel.Info) output(reline(infoPrefix, msg.toString))
  def debug(msg: Any) = if(logLevel >= LogLevel.Debug) output(reline(debugPrefix, msg.toString))
  def trace(msg: Any) = if(logLevel >= LogLevel.Trace) output(reline(tracePrefix, msg.toString))

}

class DefaultStdErrLogger extends Logger {

  import Logger._

  override val logLevel: LogLevel.Level = LogLevel.Warning

  override def output(msg: String) : Unit = {
    Console.err.println(msg)
  }

}

class VerboseStdErrLogger extends Logger {

  import Logger._

  override val logLevel: LogLevel.Level = LogLevel.Debug

  override def output(msg: String) : Unit = {
    Console.err.println(msg)
  }

}
