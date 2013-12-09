package regolic.util

trait HasLogger {
  val logger: Logger = new DefaultStdErrLogger
}

trait HasDefaultStdErrLogger extends HasLogger {
  override val logger = new DefaultStdErrLogger
}
trait HasVerboseStdErrLogger extends HasLogger {
  override val logger = new VerboseStdErrLogger
}
trait HasTraceStdErrLogger extends HasLogger {
  override val logger = new TraceStdErrLogger
}
