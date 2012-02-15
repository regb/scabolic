package regolic.asts.fol

import org.scalatest.FunSuite
import regolic.asts.core.Trees._
import Manip._
import Trees._

class ManipSuite extends FunSuite {

  //some atoms
  private val pSymbol = PredicateSymbol("p", List())
  private val qSymbol = PredicateSymbol("q", List())
  private val rSymbol = PredicateSymbol("r", List())
  private val sSymbol = PredicateSymbol("s", List())
  private val tSymbol = PredicateSymbol("t", List())
  private val p = PredicateApplication(pSymbol, List())
  private val q = PredicateApplication(qSymbol, List())
  private val r = PredicateApplication(rSymbol, List())
  private val s = PredicateApplication(sSymbol, List())
  private val t = PredicateApplication(tSymbol, List())



  test("isBasicForm: trivial formulas") {
    assert(isBasicForm(True()))
    assert(isBasicForm(False()))

    assert(isBasicForm(p))
    assert(isBasicForm(Not(p)))
    assert(isBasicForm(And(List(p, q, r))))
    assert(isBasicForm(Or(List(p, s, t))))

    assert(!isBasicForm(Implies(p, q)))
    assert(!isBasicForm(Iff(r, q)))
    assert(!isBasicForm(IfThenElse(p, q, t)))
  }

  test("isBasicForm: composed formulas") {
    assert(isBasicForm(And(List(Not(p), s, t))))
    assert(isBasicForm(And(List(Not(p), Or(List(p, s)), t))))
    assert(isBasicForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(p), Not(False()))), p, t, Not(r)))))

    assert(!isBasicForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r)))))
  }

  test("basicForm: trivial formulas") {

  }

  test("basicForm: composed formulas") {

  }

}
