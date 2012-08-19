package regolic

import scala.collection.mutable.HashMap
import scala.collection.mutable.HashMap

object Stats {


  //time is stored in nanoseconds
  private val times: HashMap[String, Long] = new HashMap

  
  def time[A](tag: String)(code: => A): A = {
    val timeBegin = System.nanoTime
    val res: A = code
    val timeElapsed = System.nanoTime - timeBegin
    times.get(tag) match {
      case None => times.put(tag, timeElapsed)
      case Some(t) => times.put(tag, t+timeElapsed)
    }
    res
  }

  //get time in seconds
  def getTime(tag: String): Double = times(tag)/1e9


  //need to handle "nested" timer
  def percents: Map[String, Int] = {
    val total: Long = times.foldLeft(0l)((a, p) => a + p._2)
    times.map(p => (p._1, (p._2.toDouble/total.toDouble*100).toInt)).toMap
  }

}
