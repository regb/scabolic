package regolic.dpllt

import regolic.asts.theories.int.Trees.IntSort
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.applyFun
import regolic.smt.qfeuf.CongruenceClosure
import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier

import org.scalatest.FunSuite

class DplltSuite extends FunSuite {

  val x = freshVariable("v", IntSort())
  val y = freshVariable("v", IntSort())
  val z = freshVariable("v", IntSort())
  val phi = And(Equals(x, y), Or(And(Equals(y, z), Not(Equals(x,
    z))), Equals(x, z)))
  val psi = And(Equals(x, y), Or(And(Equals(y, z), Not(Equals(x,
    z))), Equals(x, z)), Not(Equals(x, y)))

  test("PropositionalSkeleton") {
    val ps = PropositionalSkeleton(phi)
    // TODO assert
  }

  test("Currifier") {
    assert(
      Currifier(List(Equals(FunctionApplication(g, List(h)), d)))
      ===
      List(Equals(FunctionApplication(applyFun, List(Variable(g.name,
        g.returnSort), h)), d))
    )
  }

  test("Flattener") {
    val count = freshVariable("variable", IntSort()).name.substring(9).toInt
    val vp = Variable("variable_" + (count + 1), IntSort())
    val vpp = Variable("variable_" + (count + 2), IntSort())
    val vppp = Variable("variable_" + (count + 3), IntSort())
    val extra = Variable("variable_" + (count + 4), IntSort())
    assert(
      Flattener(List(Equals(FunctionApplication(applyFun,
        List(FunctionApplication(applyFun, List(FunctionApplication(applyFun,
          List(Variable(g.name, g.returnSort), a)),
        FunctionApplication(applyFun, List(h, b)))), b)), b)))
      ===
      List(
        Equals(FunctionApplication(applyFun, List(Variable(g.name,
          g.returnSort), a)), vp),
        Equals(FunctionApplication(applyFun, List(h, b)), vpp),
        Equals(FunctionApplication(applyFun, List(vp, vpp)), vppp),
        Equals(FunctionApplication(applyFun, List(vppp, b)), extra),
        Equals(extra, b)
      ).reverse
    )
  }

  test("small example SAT") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(phi) === true)
  }

  test("small example UNSAT") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(psi) === false)
  }

  val a = freshVariable("a", IntSort())
  val b = freshVariable("b", IntSort())
  val c = freshVariable("c", IntSort())
  val d = freshVariable("d", IntSort())
  val e = freshVariable("e", IntSort())
  val g = freshFunctionSymbol("g", List(IntSort()), IntSort())
  val h = freshVariable("h", IntSort())
  val eqs = List(Equals(FunctionApplication(g, List(h)), d), Equals(c, d),
    Equals(FunctionApplication(g, List(d)), a), Equals(e, c), Equals(e, b),
    Equals(b, h))
    
  test("larger example SAT") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(And(eqs)) === true)
  }

  //TODO test explain
}
