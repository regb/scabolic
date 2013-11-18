package regolic
package dpllt

class PropositionalLiteral(val id: Int, val polInt: Int) extends Literal {
  require(polInt == 1 | polInt == 0)
  def this(id: Int, pol: Boolean) = this(id, if(pol) 1 else 0)

  def neg = new PropositionalLiteral(id, 0)
  def pos = new PropositionalLiteral(id, 1)

  override def toString: String = (if(polarity) "" else "-") + "b_" + id
}

class PropositionalSolver extends TheorySolver {

  def initialize(ls: Set[Literal]): Unit = {}

  def isTrue(l: Literal): Boolean = true

  def backtrack(n: Int): Unit = {}

  def setTrue(l: Literal): Set[Literal] = Set()

  def explanation(l: Literal): Set[Literal] = Set()
  
}
