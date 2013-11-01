package regolic.smt.qfeuf

import regolic.asts.fol.Trees._
import regolic.asts.core.Trees._
import regolic.asts.core.Manip._

import org.scalatest.FunSuite

class FastCongruenceClosureSuite extends FunSuite {

  import FastCongruenceClosure._

  private val sort = Sort("A", List())
  private val f1Sym = FunctionSymbol("f1", List(sort), sort)
  private val f2Sym = FunctionSymbol("f2", List(sort, sort), sort)
  private val f3Sym = FunctionSymbol("f3", List(sort, sort, sort), sort)
  private def f1(t: Term): Term = FunctionApplication(f1Sym, List(t))
  private def f2(t1: Term, t2: Term): Term = FunctionApplication(f2Sym, List(t1, t2))
  private def f3(t1: Term, t2: Term, t3: Term): Term = FunctionApplication(f3Sym, List(t1, t2, t3))

  private val x = Variable("v", sort)
  private val y = Variable("v", sort)
  private val z = Variable("v", sort)

  private val aSym = FunctionSymbol("a", List(), sort)
  private val bSym = FunctionSymbol("b", List(), sort)
  private val cSym = FunctionSymbol("c", List(), sort)
  private val a = FunctionApplication(aSym, List())
  private val b = FunctionApplication(bSym, List())
  private val c = FunctionApplication(cSym, List())

  test("basic merge") {
    val cc1 = new FastCongruenceClosure
    cc1.initialize(3)
    assert(!cc1.areCongruent(Constant(0), Constant(1)))
    assert(!cc1.areCongruent(Constant(1), Constant(2)))
    assert(!cc1.areCongruent(Constant(0), Constant(2)))
    cc1.merge(0, 1)
    assert(cc1.areCongruent(Constant(0), Constant(1)))
    cc1.merge(1, 2)
    assert(cc1.areCongruent(Constant(1), Constant(2)))
    assert(cc1.areCongruent(Constant(0), Constant(2)))
    assert(cc1.areCongruent(Constant(2), Constant(0)))
  }

}
