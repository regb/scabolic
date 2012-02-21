package regolic.lp

import regolic.asts.core.Trees.Term
import regolic.asts.core.Trees.PredicateApplication
import regolic.algebra.Rational
import regolic.algebra.Vector
import regolic.algebra.Matrix

//a standard linear program is a canonical form of a linear program where we try to minimize 
//a function c.x under some constraints that can be writen Ax = b with x >= 0
//c, b and A are standard names in that situation, so we make use of them

class StandardLinearProgram(val c: Vector[Rational], val A: Matrix[Rational], val b: Vector[Rational]) {

  val nbConstraints = b.size
  val nbVariables = c.size

  require(A.nbRow == nbConstraints && A.nbCol == nbVariables)

}

object StandardLinearProgram {

  def fromMax(objectiveFunction: Term, constraints: List[PredicateApplication]): StandardLinearProgram = {
    null
  }

  def fromMin(objectiveFunction: Term, constraints: List[PredicateApplication]): StandardLinearProgram = {
    null
  }

}
