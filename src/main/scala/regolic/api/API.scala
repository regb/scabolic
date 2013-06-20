package regolic.api

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import regolic.sat.Solver
import regolic.sat.Solver.Results._
import regolic.sat.Solver.Clause
import regolic.sat.ConjunctiveNormalForm
import regolic.sat.Literal

object API {

  implicit class FormulaWrapper(f: Formula) {
    def &&(f2: Formula): Formula = And(f, f2)
    def ||(f2: Formula): Formula = Or(f, f2)
    def unary_!(): Formula = Not(f)
  }
  implicit class TermWrapper(t: Term)

  def boolVar(): Formula = freshPropositionalVariable("v")

  //TODO assumptions should only be literals not involved formulas
  //     runtime check not satisfying
  def solve(f: Formula, assumptions: List[Formula] = Nil): Option[Map[Formula, Boolean]] = {
    val (clauses, nbVars, mapping) = ConjunctiveNormalForm(f) 

    val assumps = assumptions.map{ lit => lit match {
      case Not(v) if(mapping.contains(v)) => mapping(v)
      case v@PropositionalVariable(_) if(mapping.contains(v)) => mapping(v)
      case _ => sys.error(lit +" not a literal or a new variable")
    }}.toArray
    
    println("cnf form computed")

    Solver.solve(clauses.map(lits => new Clause(lits.toList)).toList, nbVars, assumps) match {
      case Satisfiable(model) =>
        Some(mapping.map(p => (p._1, model(p._2))))
      case Unsatisfiable => None
      case Unknown =>
        sys.error("shouldn't be unknown")
    }

  }

}
