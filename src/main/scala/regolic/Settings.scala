package regolic

object Settings {

  var stats = false

  var timeout: Option[Int] = None

  var restartInterval: Int = 0
  var restartFactor: Double = 1.1

  var logger: Logger = new DefaultStdErrLogger

}
