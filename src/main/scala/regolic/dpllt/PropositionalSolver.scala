package regolic
package dpllt

class PropositionalSolver extends TheorySolver {

  def initialize(ls: Set[Literal]): Unit = {}

  def isTrue(l: Literal): Boolean = true

  def backtrack(n: Int): Unit = {}

  def setTrue(l: Literal): Set[Literal] = Set()

  def explanation(l: Literal): Set[Literal] = Set()
  
}
