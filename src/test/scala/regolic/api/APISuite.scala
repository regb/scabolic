package regolic.api

import regolic.sat.Solver.Results._
import regolic.asts.core.Trees._
import API._

import org.scalatest.FunSuite

class APISuite extends FunSuite {

  val x1 = boolVar()
  val x2 = boolVar()

  test("api unsat example with assumption") {
    val f1 = (x1 || x2) && !x1
    val result = solve(f1,List(!x2))
    assert(result === None)
  }
}

