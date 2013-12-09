package regolic.util

trait HasLogger {
  val logger: Logger = DefaultStdErrLogger
}

trait HasDefaultStdErrLogger extends HasLogger {
  override val logger: Logger = DefaultStdErrLogger
}
trait HasVerboseStdErrLogger extends HasLogger {
  override val logger: Logger = VerboseStdErrLogger
}
trait HasTraceStdErrLogger extends HasLogger {
  override val logger: Logger = TraceStdErrLogger
}
