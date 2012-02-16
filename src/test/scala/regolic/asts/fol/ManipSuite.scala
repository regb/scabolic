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

  test("isConjunctiveNormalForm: trivial formulas") {
    assert(isConjunctiveNormalForm(And(List(Or(List(True()))))))
    assert(!isConjunctiveNormalForm(True()))

    assert(isConjunctiveNormalForm(And(List(Or(List(p))))))
    assert(isConjunctiveNormalForm(And(List(Or(List(Not(p)))))))
    assert(isConjunctiveNormalForm(And(List(Or(List(p)), Or(List(q)), Or(List(r))))))
    assert(isConjunctiveNormalForm(And(List(Or(List(p, s, t))))))

    assert(!isConjunctiveNormalForm(Or(List(p, q))))
    assert(!isConjunctiveNormalForm(And(List(p, q))))
    assert(!isConjunctiveNormalForm(Not(p)))
    assert(!isConjunctiveNormalForm(Implies(p, q)))
    assert(!isConjunctiveNormalForm(Iff(r, q)))
    assert(!isConjunctiveNormalForm(IfThenElse(p, q, t)))
  }

  test("isConjunctiveNormalForm: composed formulas") {
    assert(isConjunctiveNormalForm(And(List(Or(List(Not(p), q, r)), Or(List(s, t))))))
    assert(isConjunctiveNormalForm(And(List(Or(List(Not(p), Not(q), p)), Or(List(p, s)), Or(List(t))))))
    assert(isConjunctiveNormalForm(And(List(Or(List(Not(p), True(), p)), Or(List(p, s)), Or(List(False(), t))))))

    assert(!isConjunctiveNormalForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r)))))
  }

  test("conjunctiveNormalForm: trivial formulas") {
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(True())))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(False())))

    assert(isConjunctiveNormalForm(conjunctiveNormalForm(p)))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(And(List(p, q, r)))))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(Or(List(p, q, r)))))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(Not(p))))

    assert(isConjunctiveNormalForm(conjunctiveNormalForm(Implies(p, t))))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(Iff(p, r))))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(IfThenElse(r, s, t))))

  }

  test("conjunctiveNormalForm: composed formulas") {
    //assert(isConjunctiveNormalForm(conjunctiveNormalForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r))))))
  }
}
