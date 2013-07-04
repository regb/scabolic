package regolic.dpllt

import regolic.asts.theories.int.Trees.IntSort
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import org.scalatest.FunSuite

class DplltSuite extends FunSuite {

  val x = freshVariable("v", IntSort())
  val y = freshVariable("v", IntSort())
  val z = freshVariable("v", IntSort())
  val phi = And(Equals(x, y), Or(And(Equals(y, z), Not(Equals(x,
    z))), Equals(x, z)))

  test("propositional skeleton") {
    val ps = PropositionalSkeleton(phi)
    // TODO assert
  }

  test("lazy basic solver") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(phi) === true)
  }
}
