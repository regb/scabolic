package regolic
package dpllt

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import scala.collection.mutable.Stack

// Interface similar to the one described in "DPLL(T): Fast Decision Procedures"
// by Ganzinger, Hagen, Nieuwenhuis, Oliveras, Tinelli
trait TheorySolver {

  def initialize(ls: Set[Literal]): Unit

  def isTrue(l: Literal): Boolean

  def backtrack(n: Int): Unit

  def setTrue(l: Literal): Set[Literal]

  def explanation(l: Literal): Set[Literal]
  
  //def backtrackTo(l: Formula): Unit

  //def explain(): Set[Formula]

  //def explain(l: Formula, lPrime: Formula = null): Set[Formula]

  //var time: Double
}
