package regolic.lp

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.theories.real.Trees._
import regolic.algebra.Rational
import regolic.algebra.Vector
import regolic.algebra.Matrix

object Solver {

  sealed trait Result
  case object Unbounded extends Result
  case object Infeasible extends Result
  case class Optimal(assignment: Map[Variable, Rational]) extends Result

  def maximize(objectiveFunction: Term, constraints: List[PredicateApplication]): Result = minimize(Neg(objectiveFunction), constraints)
  def minimize(objectiveFunction: Term, constraints: List[PredicateApplication]): Result = {
    val initialVars: Set[Variable] = (vars(objectiveFunction) ++ constraints.map(vars).flatten)
    val (lp, allVars, mappingVars) = StandardLinearProgram.fromMin(objectiveFunction, constraints)
    Simplex(lp) match {
      case Simplex.Infeasible => Infeasible
      case Simplex.Unbounded => Unbounded
      case Simplex.Optimal(assignment) => {
        val finalAssignment = initialVars.map(v => {
          val index = allVars.indexOf(v)
          if(index == -1) {
            val (v1, v2) = mappingVars(v)
            val indexV1 = allVars.indexOf(v1)
            val indexV2 = allVars.indexOf(v2)
            (v, assignment(indexV1) - assignment(indexV2))
          } else {
            (v, assignment(index))
          }
        }).toMap
        Optimal(finalAssignment)
      }
    }
  }

}
