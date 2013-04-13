package regolic.api

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import regolic.sat.DPLL._
import regolic.sat.DPLL
import regolic.sat.ConjunctiveNormalForm
import regolic.sat.Literal

object API {

  case class FormulaWrapper(f: Formula) {
    def &&(f2: Formula): Formula = And(f, f2)
    def ||(f2: Formula): Formula = Or(f, f2)
    def unary_!(): Formula = Not(f)
  }
  case class TermWrapper(t: Term)

  implicit def wrapFormula(f: Formula) = FormulaWrapper(f)
  implicit def wrapTerm(t: Term) = TermWrapper(t)

  def boolVar(): Formula = freshPropositionalVariable("v")

  def solve(f: Formula): Option[Map[Formula, Boolean]] = {
    val (clauses, nbVars, mapping) = ConjunctiveNormalForm(f)

    println("cnf form computed")
    isSat(clauses.map(lits => new Clause(lits.toList)).toList, nbVars) match {
      case None => None
      case Some(model) =>
        Some(mapping.map(p => (p._1, model(p._2))))
    }

  }

}
