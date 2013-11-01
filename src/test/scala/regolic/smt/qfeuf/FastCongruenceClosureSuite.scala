package regolic.smt.qfeuf

import regolic.asts.fol.Trees._
import regolic.asts.core.Trees._
import regolic.asts.core.Manip._

import org.scalatest.FunSuite

class FastCongruenceClosureSuite extends FunSuite {

  //test if the term contains a function of arity more than 1 which is not Apply
  private def containsNonApplyFunctions(t: Term): Boolean = t match {
    case Apply(t1, t2) => containsNonApplyFunctions(t1) || containsNonApplyFunctions(t2)
    case Variable(_, _) => false
    case FunctionApplication(_, Nil) => false
    case _ => true
  }
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

  private def substituteApply(t: Term): Term = {
    mapPostorder(t, f => f, {
      case Apply(FunctionApplication(FunctionSymbol(name, params, FunctionSort(from, to)), args), arg) => {
        val newSymbol = FunctionSymbol(name, params ::: List(from), to)
        FunctionApplication(newSymbol, args ::: List(arg))
      }
      case t => t
    })
  }
        
  test("basic setTrue") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Not(Equals(a, a))))
    assert(cc1.setTrue(Not(Equals(a, a))) === None)

    val cc2 = new CongruenceClosure
    cc2.initialize(Set(Equals(a, a)))
    assert(cc2.setTrue(Equals(a, a)) != None)
  }

}
