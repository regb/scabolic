package regolic
package dpllt

/*
 * id is unique per predicate, different literals with same predicate but different polarity
 * will have the same id
 */
abstract class Literal(val id: Int, val polInt: Int) {
  require(id >= 0)
  require(polInt == 0 || polInt == 1)

  def this(id: Int, polarity: Boolean) = this(id, if(polarity) 1 else 0)

  def polarity = polInt == 1

  override def toString: String = (if(!polarity) "-" else "") + "v" + id

}
