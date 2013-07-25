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

  test("propositional skeleton") {
    val ps = PropositionalSkeleton(phi)
    // TODO assert
  }

  test("lazy basic solver SAT") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(phi) === true)
  }

  test("lazy basic solver UNSAT") {
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
    
  test("CC") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(And(eqs)) === true)
  }

  test("Currifier") {
    println("Currify: "+ Currifier(eqs.map{case Equals(t1, t2) => (t1, t2)}))
  }

  test("Flattener") {
  }
  //TODO test explain, currifier, flattener
}
