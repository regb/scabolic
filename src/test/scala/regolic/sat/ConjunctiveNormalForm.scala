package regolic.sat

import regolic.asts.fol.Trees._
import regolic.asts.core.Trees._

import org.scalatest.FunSuite

class ConjunctiveNormalFormSuite extends FunSuite {

  val q1 = freshPropositionalVariable("Q")
  val q2 = freshPropositionalVariable("Q")
  val q3 = freshPropositionalVariable("Q")
  val r1 = freshPropositionalVariable("R")
  val r2 = freshPropositionalVariable("R")

  def checkEncoding(f: Formula, isSat: Boolean) {
    val (cnf, nb, map) = ConjunctiveNormalForm(f)
    val model = DPLL.isSat(cnf.map(lits => new DPLL.Clause(lits.toList)).toList, nb)
    if(isSat) {
      if(model == None) {
        println(f + " was not encoded correctly")
        println("encoding was: " + cnf)
        println("with: " + map)
        assert(false)
      }
    } else {
      if(model != None) {
        println(f + " was not encoded correctly")
        println("encoding was: " + cnf)
        println("with: " + map)
        assert(false)
      }
    }
  }

  test("cnf") {
    val f1 = Or(And(q1,q2,q3), And(r1,r2))
    checkEncoding(f1, true)
    val f2 = And(Or(q1,q2,q3), Or(q1,Not(q2)), Or(q2, Not(q3)))
    checkEncoding(f2, true)
    val f3 = And(Or(Not(q1),q3), Or(q1,Not(q2)), Or(q2, Not(q3)), Or(q3, q2), Or(Not(q1), Not(q2)))
    checkEncoding(f3, false)
  }

}
