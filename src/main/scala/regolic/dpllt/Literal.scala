package regolic
package dpllt

/*
 * id is unique per predicate, different literals with same predicate but different polarity
 * will have the same id
 */
abstract class Literal {

  val id: Int 

  val polInt: Int

  def polarity: Boolean = polInt == 1

  override def toString: String = (if(!polarity) "-" else "") + "v" + id

  //returns the positive literal (always true)
  def pos: Literal

  //returns the negative literal (always false)
  def neg: Literal

}
