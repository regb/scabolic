package regolic.smt.qflra

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip.disjunctiveNormalForm
import regolic.asts.theories.real.Trees._
import regolic.asts.theories.real.Manip.simplify
import regolic.asts.theories.real.Eval

import regolic.lp.Solver._
import regolic.algebra.Rational

import regolic.parsers.SmtLib2.Trees.QF_LRA

object SimplexSolver extends regolic.smt.Solver {

  val logic = QF_LRA

  def isSat(f: Formula): Pair[Boolean, Option[Map[Formula, List[Formula]]]] = {
    val Or(ands) = disjunctiveNormalForm(f)

    var modelFound = false
    var model: Map[Variable, Term] = null

    for(And(lits) <- ands if !modelFound) {
      val preprocessLits = lits.map{
        case Not(LessEqual(t1, t2)) => LessThan(Zero(), Sub(t1, t2))
        case Not(LessThan(t1, t2)) => LessEqual(Sub(t2, t1), Zero())
        case Not(GreaterEqual(t1, t2)) => LessThan(Zero(), Sub(t2, t1))
        case Not(GreaterThan(t1, t2)) => LessEqual(Sub(t1, t2), Zero())
        case LessEqual(t1, t2) => LessEqual(Sub(t1, t2), Zero())
        case LessThan(t1, t2) => LessThan(Zero(), Sub(t2, t1))
        case GreaterEqual(t1, t2) => LessEqual(Sub(t2, t1), Zero())
        case GreaterThan(t1, t2) => LessThan(Zero(), Sub(t1, t2))
      }

      /* Now we use the observation that a set {p1 > 0, ..., pn > 0} is SAT iff there
       * exists a x > 0 s.t. {p1 >= x, ..., pn >= x} is SAT.
       * We introduce a new var and use it as the maximal function, if it is not > 0 at
       * the end of the run then it was impossible to SAT the problem
       */

      //println(preprocessLits)
      val allVars: Set[Variable] = lits.flatMap(vars).toSet
      val vars2zero: Map[Variable, Rational] = allVars.map(v => (v, Rational.zero)).toMap
      if(!preprocessLits.exists{ case LessThan(_, _) => true case _ => false }) { //if no strict inequality
        val finalLits = preprocessLits.map{
          case LessEqual(t, _) => {
            val cstValue = Eval(t, vars2zero)
            LessEqual(simplify(Sub(t, Num(cstValue))), Num(-cstValue))
          }
        }
        minimize(One(), finalLits) match {
          case Infeasible => ()
          case Optimal(map) => {
            modelFound = true
            model = map.map{case (v, r) => (v, Num(r)) }
          }
          case Unbounded => sys.error("1 is not unbounded!")
        }
      } else {
        val checkVar = freshVar("x")
        val finalLits = LessEqual(Zero(), checkVar) :: preprocessLits.map{
          case LessEqual(t, _) => {
            val cstValue = Eval(t, vars2zero)
            LessEqual(simplify(Sub(t, Num(cstValue))), Num(-cstValue))
          }
          case LessThan(_, t) => {
            val newTerm = Sub(t, checkVar)
            val cstValue = Eval(t, vars2zero)
            LessEqual(simplify(Neg(Sub(newTerm, Num(cstValue)))), Num(cstValue))
          }
        }
        //println(finalLits)
        maximize(checkVar, finalLits) match {
          case Infeasible => ()
          case Optimal(map) => {
            if(map(checkVar) > Rational.zero) {
              modelFound = true
              model = (map - checkVar).map{ case (v, r) => (v, Num(r)) }
            }
          }
          case Unbounded => { //trick is to minimize chckvar but with a new constraint that checkvar >= 1 since we know it is unbounded
            minimize(checkVar, LessEqual(Neg(checkVar), Num(-Rational.one)) :: finalLits) match {
              case Infeasible => sys.error("Should not happen")
              case Unbounded => sys.error("should not happen")
              case Optimal(map) => {
                assert(map(checkVar) > Rational.zero)
                modelFound = true
                model = (map - checkVar).map{ case (v, r) => (v, Num(r)) }
              }
            }
          }
        }
      }
    }

    if(modelFound) 
      (true, None)
    else
      (false, None) // TODO Explanations
  }

}
