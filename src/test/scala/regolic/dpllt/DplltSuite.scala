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
  val psi = And(phi, Not(Equals(x, y)))

  val a = freshVariable("a", IntSort())
  val b = freshVariable("b", IntSort())
  val c = freshVariable("c", IntSort())
  val d = freshVariable("d", IntSort())
  val e = freshVariable("e", IntSort())
  val g = freshFunctionSymbol("g", List(IntSort()), IntSort())
  val gVar = Variable(g.name, g.returnSort)
  val h = freshVariable("h", IntSort())
  val eqs = List(Equals(FunctionApplication(g, List(h)), d), Equals(c, d),
    Equals(FunctionApplication(g, List(d)), a), Equals(e, c), Equals(e, b),
    Equals(b, h))

  test("PropositionalSkeleton") {
    val ps = PropositionalSkeleton(phi)
    // TODO assert
  }

  test("Currifier") {
    val fun = freshFunctionSymbol("fun", List(IntSort(), IntSort()), IntSort())

    assert(
      Currifier(List(Equals(FunctionApplication(fun, List(a, b)), d)))
      ===
      List(Equals(
        FunctionApplication(applyFun, List(FunctionApplication(applyFun,
          List(Variable(fun.name, fun.returnSort), a)), b)), d)
      )
    )
  }

  test("Flattener") {
    val count = freshVariable("variable", IntSort()).name.substring(9).toInt
    val vp = Variable("variable_" + (count + 1), IntSort())
    val vpp = Variable("variable_" + (count + 2), IntSort())
    val vppp = Variable("variable_" + (count + 3), IntSort())
    val extra = Variable("variable_" + (count + 4), IntSort())

    assert(
      Flattener(
        List(Equals(
          FunctionApplication(applyFun,
            List(FunctionApplication(applyFun,
              List(FunctionApplication(applyFun,
                List(gVar, a)),
              FunctionApplication(applyFun, List(h, b)))), b)), b)
        )
      )
      ===
      List(
        Equals(FunctionApplication(applyFun, List(gVar, a)), vp),
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

  test("larger example SAT") {
    val lazySolver = new LazyBasicSolver()
    assert(lazySolver.solve(And(eqs)) === true)
  }

  test("explain") {
    val inputEqs = List(
      Equals(FunctionApplication(applyFun, List(gVar, h)), d),
      Equals(c, d),
      Equals(FunctionApplication(applyFun, List(gVar, d)), a),
      Equals(e, c),
      Equals(e, b),
      Equals(b, h)
    
      /*
       *Equals(FunctionApplication(applyFun, List(gVar, h)), d),
       *Equals(FunctionApplication(applyFun, List(gVar, d)), a),
       *Equals(e, b),
       *Equals(e, c),
       *Equals(c, d),
       *Equals(b, h)
       */
    )
    val cc = new CongruenceClosure(inputEqs)
    inputEqs.foreach(cc.merge)
    
    assert(
      cc.explain(a, b)
      ===
      List(
        Equals(FunctionApplication(applyFun, List(gVar, h)), d),
        Equals(FunctionApplication(applyFun, List(gVar, d)), a),
        Equals(e, b),
        Equals(e, c),
        Equals(c, d),
        Equals(b, h)
      )
    )
  }

}
