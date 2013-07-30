package regolic.dpllt

import regolic.asts.theories.int.Trees.IntSort
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Apply
import regolic.smt.qfeuf.CongruenceClosure
import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier

import regolic.sat.NaiveSolver
import regolic.sat.Literal

import org.scalatest.FunSuite
import scala.util.Random

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

  //val rand = new Random(scala.compat.Platform.currentTime)
  val rand = new Random(0)

  test("PropositionalSkeleton") {
    val termToValue = scala.collection.mutable.Map[Term, Int]()
    def evaluate(f: Formula): Boolean = {
      f match {
        case Equals(t1, t2) => {
          if(!termToValue.contains(t1))
            termToValue(t1) = rand.nextInt(10)
          if(!termToValue.contains(t2))
            termToValue(t2) = rand.nextInt(10)
          (termToValue(t1) == termToValue(t2))
        }
        case Not(f) => {
          !evaluate(f)
        }
        case And(fs) => {
          // Scala is too smart for foldLeft being useful here
          // fs.foldLeft(true)((l, f) => l && evaluate(f))
          fs.map(evaluate).reduceLeft((l,bool) => l && bool)
        }
        case Or(fs) => {
          // Scala is too smart for foldLeft being useful here
          // fs.foldLeft(false)((l, f) => l || evaluate(f))
          fs.map(evaluate).reduceLeft((l,bool) => l || bool)
        }
        //case Implies(t1, t2) => {
          //(!evaluate(t1) || evaluate(t2))
        //}
        //case Iff(t1, t2) => {
          //(evaluate(t1) == evaluate(t2))
        //}
        case _ => sys.error("Unhandled case in PropositionalSkeleton: " + f)
      }
    }
    val truthValTheory = evaluate(phi)

    val (constraints, litCount, idToEq) = PropositionalSkeleton(phi)

    val idToTruthVal = idToEq.map{
      case (litId, eq) => eq match {
        case Equals(t1, t2) => (litId, termToValue(t1) == termToValue(t2))
      }
    }
    val constraintsGivenModel = constraints.withFilter{ s =>
      !s.exists{lit => {
          if(idToTruthVal.contains(lit.id))
            idToTruthVal(lit.id) == lit.polarity
          else
            false
        }
      }
    }.map{ s =>
      s.filter{lit => {
        if(idToTruthVal.contains(lit.id))
          idToTruthVal(lit.id) == lit.polarity
        else
          true
      }
    }
    }

    val truthValProp = NaiveSolver.isSat(constraintsGivenModel)

    assert(truthValTheory === truthValProp.nonEmpty)
  }

  test("Currifier") {
    def noFunctionOtherThanApply(f: Term): Boolean = {
      f match {
        case Apply(t1, t2) => noFunctionOtherThanApply(t1) && noFunctionOtherThanApply(t2)
        case Variable(_, _) => true
        case _ => false
      }
    }
    val fun = freshFunctionSymbol("fun", List(IntSort(), IntSort()), IntSort())

    assert(
      Currifier(
        List(Equals(FunctionApplication(fun, List(a, b)), d))
      ).forall{
        case Equals(t1, t2) => noFunctionOtherThanApply(t1) && noFunctionOtherThanApply(t2)
      }
    )
  }

  test("Flattener") {
    def noNestedFunctions(eq: PredicateApplication): Boolean = {
      eq match {
        case Equals(Variable(_, _), Variable(_, _)) => true
        case Equals(Apply(Variable(_, _), Variable(_, _)), Variable(_, _)) => true
        case _ => false
      }
    }
    assert(
      Flattener(
        List(Equals(
            Apply(Apply(Apply(gVar, a), Apply(h, b)), b), b
          )
        )
      ).forall(noNestedFunctions)
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
      Equals(Apply(gVar, h), d),
      Equals(c, d),
      Equals(Apply(gVar, d), a),
      Equals(e, c),
      Equals(e, b),
      Equals(b, h)
    )
    val cc = new CongruenceClosure(inputEqs)
    inputEqs.foreach(cc.merge)
    
    // Check that the right equalities are in the explanation, w/o caring about
    // order
    assert(
      cc.explain(a, b).toSet
      ===
      Set(
        Equals(Apply(gVar, h), d),
        Equals(Apply(gVar, d), a),
        Equals(e, b),
        Equals(e, c),
        Equals(c, d),
        Equals(b, h)
      )
    )
  }

}
