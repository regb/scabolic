package regolic.util

/*
 * Logging should be used for extra information, not serving as a reporting tool for the
 * tool usage. In particular, in a CLI style of use, we should use stdin and stdout for
 * regular input-output (sat/unsat, model printing depending on arguments, etc), and logging
 * should be sent to a different stream (and be configurable or turned off). logging level
 * INFO is not to be used for regular output of the system (again, like sat/unsat).
 *
 * Choice of logging level is as follows: TODO
 *
 */

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
      else if(prefix == debugPrefix)
        Console.MAGENTA
      else if(prefix == tracePrefix)
        Console.GREEN
      else //for INFO
        Console.BLUE
    "[" + color + prefix.substring(1, prefix.length-2) + Console.RESET + "] " +
    msg.trim.replaceAll("\n", "\n" + (" " * (prefix.size)))
  }

  def error(msg: => String, args: Any*) = if(logLevel >= LogLevel.Error) output(reline(errorPrefix, msg.format(args: _*)))
  def warning(msg: => String, args: Any*) = if(logLevel >= LogLevel.Warning) output(reline(warningPrefix, msg.format(args: _*)))
  def info(msg: => String, args: Any*) = if(logLevel >= LogLevel.Info) output(reline(infoPrefix, msg.format(args: _*)))
  def debug(msg: => String, args: Any*) = if(logLevel >= LogLevel.Debug) output(reline(debugPrefix, msg.format(args: _*)))
  def trace(msg: => String, args: Any*) = if(logLevel >= LogLevel.Trace) output(reline(tracePrefix, msg.format(args: _*)))

}

abstract class StdErrLogger extends Logger {
  override def output(msg: String) : Unit = {
    Console.err.println(msg)
  }
}

class DefaultStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel.Level = LogLevel.Warning
}

class VerboseStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel.Level = LogLevel.Debug
}

class TraceStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel.Level = LogLevel.Trace
}
