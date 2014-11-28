package cafesat.api

import regolic.asts.core.Trees.{Formula => CoreFormula, _}
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip.{simplify => folSimplify, _}

import regolic.sat.Solver
import regolic.sat.Solver.Results._
import regolic.sat.Solver.Clause
import regolic.sat.ConjunctiveNormalForm
import regolic.sat.Literal

import scala.language.implicitConversions

object API {

  type Formula = CoreFormula

  implicit class FormulaWrapper(f: Formula) {
    def &&(f2: Formula): Formula = And(f, f2)
    def ||(f2: Formula): Formula = Or(f, f2)
    def unary_!(): Formula = Not(f)

    def iff(f2: Formula): Formula = Or(And(f, f2), And(Not(f), Not(f2)))
    def xor(f2: Formula): Formula = Or(And(f, Not(f2)), And(Not(f), f2))
  }

  def or(fs: Formula*): Formula = Or(fs: _*)
  def and(fs: Formula*): Formula = And(fs: _*)
  
  implicit class TermWrapper(t: Term)

  implicit def bool2formula(b: Boolean) = if(b) True() else False()
  implicit def boolList2formulaList(bs: List[Boolean]): List[Formula] = bs.map(b => if(b) True() else False())
  
  
  def boolVar(prefix: String = "P"): Formula = freshPropositionalVariable(prefix)
  
  type Model = Map[Formula, Boolean]

  def solveForSatisfiability(f: Formula): Option[Map[Formula, Boolean]] = {
    val simpleF = simplify(f)
    simpleF match {
      case True() => Some(Map()) //TODO: provide random values
      case False() => None
      case _ => {
        val (clauses, nbVars, mapping) = ConjunctiveNormalForm(simplify(f))

        //val out = new java.io.PrintWriter("scheduling.cnf", "UTF-8")

        //out.println("p cnf %d %d".format(nbVars, clauses.size))
        //clauses.foreach(lits => {
        //  out.println(lits.map(lit => 
        //    (if(lit.polarity) "" else "-") + (lit.getID+1)
        //  ).mkString("", " ", " 0"))
        //})
        //out.close()

        val s = new Solver(nbVars)
        clauses.foreach(s.addClause(_))
        val solveRes = s.solve()
        solveRes match {
          case Satisfiable(model) =>
            Some(mapping.map(p => (p._1, model(p._2))))
          case Unsatisfiable => None
          case Unknown =>
            sys.error("shouldn't be unknown")
        }
      }
    }
  }

  def simplify(f: Formula): Formula = folSimplify(f)
  
  //TODO assumptions should only be literals not involved formulas
  //     runtime check not satisfying
  //def solve(f: Formula, assumptions: List[Formula] = Nil): Option[Map[Formula, Boolean]] = {
  //  val (clauses, nbVars, mapping) = ConjunctiveNormalForm(f) 
  
  //  // TODO assumps must be Array[Literal]
  //  //      find better way than via map (taken from dimacs)
  //  val assumps = assumptions.map{ lit => lit match {
  //    case Not(v) if(mapping.contains(v)) => mapping(v)
  //    case v@PropositionalVariable(_) if(mapping.contains(v)) => mapping(v)
  //    case _ => sys.error(lit +" not a literal or a new variable")
  //  }}.map(i => if(i > 0) new Literal(i-1, true) else new Literal(-i-1, false)).toArray
  //  
  //  println("cnf form computed")
  
  //  val s = new Solver(nbVars)
  //  clauses.foreach(s.addClause(_))
  //  s.solve(assumps.asInstanceOf[Array[Literal]]) match {
  //    case Satisfiable(model) =>
  //      Some(mapping.map(p => (p._1, model(p._2))))
  //    case Unsatisfiable => None
  //    case Unknown =>
  //      sys.error("shouldn't be unknown")
  //  }
  
}
