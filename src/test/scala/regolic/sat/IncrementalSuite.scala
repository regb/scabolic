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
    val s = new Solver(2)

    val clList = List(List(na, b))
    val clauses = clList.map(lits => new Clause(lits))
    clauses.foreach(s.addClause(_))
    val result1 = s.solve(Array.empty[Int])
    assert(result1.isInstanceOf[Solver.Results.Satisfiable])

    s.addClause(new Clause(List(na, nb)))
    val result2 = s.solve(Array(a.id))
    assert(result2 equals Solver.Results.Unsatisfiable)
  }

  test("empty solve call") {
    val s = new Solver(0)
    val result = s.solve(Array.empty[Int])
    // vacuously true (sat) should be okay
    assert(result.isInstanceOf[Solver.Results.Satisfiable])
  }

  // TODO add a test where clauses are learnt by the solver
}
