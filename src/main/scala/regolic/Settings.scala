package regolic

object Settings {

  var debugLevel = 0
  var debugTags: Set[String] = Set()

  var stats = false

  var timeout: Option[Int] = None

  var restartInterval: Int = 0
  var restartFactor: Double = 1.1

}
