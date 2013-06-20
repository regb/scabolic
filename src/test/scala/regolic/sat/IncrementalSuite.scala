package regolic.sat

import Solver.Results._
import Solver.Clause

import org.scalatest.FunSuite

class IncrementalSuite extends FunSuite {

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)
  private val c = new Literal(2, true)
  private val nc = new Literal(2, false)
  private val emptyClause = Set[Literal]()

  test("Incremental run sat/unsat with assumption") {
    val clList = List(List(na, b), List(nb, c))
    val clauses = clList.map(lits => new Clause(lits))
    val result1 = Solver.solve(clauses, 3, Array.empty[Int])
    assert(result1.isInstanceOf[Solver.Results.Satisfiable])

    Solver.addClause(new Clause(List(na, nc)))
    val result2 = Solver.solve(Array(a.id))
    assert(result2 equals Solver.Results.Unsatisfiable)
  }
}
