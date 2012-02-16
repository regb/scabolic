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

  val sort = Sort("sort")
  private val x = Variable("x", sort)


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
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r))))))
    assert(isConjunctiveNormalForm(conjunctiveNormalForm(And(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r))))))
  }

  test("isDisjunctiveNormalForm: trivial formulas") {
    assert(isDisjunctiveNormalForm(Or(List(And(List(True()))))))
    assert(!isDisjunctiveNormalForm(True()))

    assert(isDisjunctiveNormalForm(Or(List(And(List(p))))))
    assert(isDisjunctiveNormalForm(Or(List(And(List(Not(p)))))))
    assert(isDisjunctiveNormalForm(Or(List(And(List(p)), And(List(q)), And(List(r))))))
    assert(isDisjunctiveNormalForm(Or(List(And(List(p, s, t))))))

    assert(!isDisjunctiveNormalForm(Or(List(p, q))))
    assert(!isDisjunctiveNormalForm(And(List(p, q))))
    assert(!isDisjunctiveNormalForm(Not(p)))
    assert(!isDisjunctiveNormalForm(Implies(p, q)))
    assert(!isDisjunctiveNormalForm(Iff(r, q)))
    assert(!isDisjunctiveNormalForm(IfThenElse(p, q, t)))
  }

  test("isDisjunctiveNormalForm: composed formulas") {
    assert(isDisjunctiveNormalForm(Or(List(And(List(Not(p), q, r)), And(List(s, t))))))
    assert(isDisjunctiveNormalForm(Or(List(And(List(Not(p), Not(q), p)), And(List(p, s)), And(List(t))))))
    assert(isDisjunctiveNormalForm(Or(List(And(List(Not(p), True(), p)), And(List(p, s)), And(List(False(), t))))))

    assert(!isDisjunctiveNormalForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r)))))
  }

  test("disjunctiveNormalForm: trivial formulas") {
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(True())))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(False())))

    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(p)))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(And(List(p, q, r)))))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(Or(List(p, q, r)))))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(Not(p))))

    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(Implies(p, t))))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(Iff(p, r))))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(IfThenElse(r, s, t))))

  }

  test("disjunctiveNormalForm: composed formulas") {
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r))))))
    assert(isDisjunctiveNormalForm(disjunctiveNormalForm(And(List(And(List(Or(List(Not(p), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r))))))
  }

  test("isQuantifierFree: trivial formulas") {
    assert(isQuantifierFree(True()))
    assert(isQuantifierFree(False()))

    assert(isQuantifierFree(p))
    assert(isQuantifierFree(Not(p)))
    assert(isQuantifierFree(And(List(p, q, r))))
    assert(isQuantifierFree(Or(List(p, s, t))))

    assert(isQuantifierFree(Implies(p, q)))
    assert(isQuantifierFree(Iff(r, q)))
    assert(isQuantifierFree(IfThenElse(p, q, t)))

    assert(!isQuantifierFree(Exists(x, p)))
    assert(!isQuantifierFree(Forall(x, p)))
  }

  test("isQuantifierFree: composed formulas") {
    assert(isQuantifierFree(And(List(Not(p), s, t))))
    assert(isQuantifierFree(And(List(Not(p), Or(List(p, s)), t))))
    assert(isQuantifierFree(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(p), Not(False()))), p, t, Not(r)))))

    assert(!isQuantifierFree(Or(List(And(List(Or(List(Not(Exists(x, p)), True(), q)), p, Not(Or(List(p, Implies(r, t)))), Not(False()))), p, t, Not(r)))))
    assert(!isQuantifierFree(Or(List(And(List(Or(List(Not(p), True(), q)), p, Not(p), Not(Forall(x, False())))), p, t, Not(r)))))
  }

  test("simplify: soundness") {

  }

  test("simplify: node reduction") {

  }

  test("isNegationNormalForm: trivial term") {
    assert(isNegationNormalForm(True()))
    assert(isNegationNormalForm(False()))

    assert(isNegationNormalForm(p))
    assert(isNegationNormalForm(Not(p)))
    assert(isNegationNormalForm(And(List(p, q, r))))
    assert(isNegationNormalForm(Or(List(p, s, t))))

    assert(!isNegationNormalForm(Implies(p, q)))
    assert(!isNegationNormalForm(Iff(r, q)))
    assert(!isNegationNormalForm(IfThenElse(p, q, t)))

    assert(isNegationNormalForm(Exists(x, p)))
    assert(isNegationNormalForm(Forall(x, p)))
  }

  test("isNegationNormalForm: composed term") {
    assert(isNegationNormalForm(Or(List(Not(p), True(), Not(False()), And(List(Not(q), p))))))
    assert(!isNegationNormalForm(Or(List(Not(p), True(), Not(False()), And(List(Not(Or(List(p, q))), p))))))
    assert(!isNegationNormalForm(Not(Or(List(Not(p), True(), Not(False()), And(List(Or(List(p, q)), p)))))))
  }

  test("negationNormalForm: trivial term") {
    assert(isNegationNormalForm(negationNormalForm(True())))
    assert(isNegationNormalForm(negationNormalForm(False())))

    assert(isNegationNormalForm(negationNormalForm(p)))
    assert(isNegationNormalForm(negationNormalForm(Not(p))))
    assert(isNegationNormalForm(negationNormalForm(And(List(p, q, r)))))
    assert(isNegationNormalForm(negationNormalForm(Or(List(p, s, t)))))

    assert(isNegationNormalForm(negationNormalForm(Implies(p, q))))
    assert(isNegationNormalForm(negationNormalForm(Iff(r, q))))
    assert(isNegationNormalForm(negationNormalForm(IfThenElse(p, q, t))))

    assert(isNegationNormalForm(negationNormalForm(Exists(x, p))))
    assert(isNegationNormalForm(negationNormalForm(Forall(x, p))))
  }

  test("negationNormalForm: composed term") {
    assert(isNegationNormalForm(negationNormalForm(Or(List(Not(p), True(), Not(False()), And(List(Not(Or(List(p, q))), p)))))))
    assert(isNegationNormalForm(negationNormalForm(Not(Or(List(Not(p), True(), Not(False()), And(List(Not(Or(List(p, q))), p))))))))
  }

}
