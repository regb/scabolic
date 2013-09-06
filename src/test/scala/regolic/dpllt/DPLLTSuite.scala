package regolic.dpllt

import regolic.asts.theories.int.Trees.IntSort
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Apply
import regolic.smt.qfeuf.CongruenceClosure
import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier
import regolic.smt.qfeuf.FastCongruenceSolver

import regolic.sat.NaiveSolver
import regolic.sat.Literal

import scala.util.Random

import regolic.helper.FunSuiteWithIDReset

class DPLLTSuite extends FunSuiteWithIDReset {

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

  val rand = new Random(compat.Platform.currentTime)

  private def propositionalSkeletonTest(f: Formula): Boolean = {
    val assignment = collection.mutable.Map[Term, Int]()
    def evaluate(f: Formula): Boolean = {
      f match {
        case Equals(t1, t2) => {
          if(!assignment.contains(t1))
            assignment(t1) = rand.nextInt(10)
          if(!assignment.contains(t2))
            assignment(t2) = rand.nextInt(10)
          (assignment(t1) == assignment(t2))
        }
        case Not(f) => {
          !evaluate(f)
        }
        case And(fs) => {
          fs.map(evaluate).reduceLeft((l,bool) => l && bool)
        }
        case Or(fs) => {
          fs.map(evaluate).reduceLeft((l,bool) => l || bool)
        }
        case _ => sys.error("Unhandled case in PropositionalSkeleton: " + f)
      }
    }
    def applyAssignment(cnf: Set[Set[Literal]], assignment: Map[Int, Boolean]): Set[Set[Literal]] = {
      cnf.withFilter{s =>
        !s.exists{lit => {
            if(assignment.contains(lit.getID))
              assignment(lit.getID) == lit.polarity
            else
              false
          }
        }
      }.map{s =>
        s.filter{lit => {
            if(assignment.contains(lit.getID))
              assignment(lit.getID) == lit.polarity
            else
              true
          }
        }
      }
    }

    val truthValTheory = evaluate(f)

    val (constraints, encoding) = PropositionalSkeleton(f)
    println("theory: "+ encoding.theory.mkString("\n", "\n", "\n"))
    println("theoryOrig: "+ encoding.theoryOrig.mkString("\n", "\n", "\n"))
    println("constraints: "+ constraints.mkString("\n", "\n", "\n"))
    val idToTruthVal = encoding.theory.zipWithIndex.map{
      case (eq, litId) => eq match {
        case Equals(t1, t2) => (litId, assignment(t1) == assignment(t2))
      }
    }.toMap
    val truthValProp = NaiveSolver.isSat(applyAssignment(constraints, idToTruthVal))

    truthValTheory == truthValProp.nonEmpty
  }

  test("PropositionalSkeleton phi") {
    assert(propositionalSkeletonTest(phi))
  }

  test("PropositionalSkeleton psi") {
    assert(propositionalSkeletonTest(psi))
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
        Equals(FunctionApplication(fun, List(a, b)), d)
      ) match {
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
        Equals(
          Apply(Apply(Apply(gVar, a), Apply(h, b)), b), b
        )
      ).forall(noNestedFunctions)
    )
  }

  test("small example SAT") {
    assert(LazyBasicSolver.solve(FastCongruenceSolver, phi) === true)
  }

  test("small example UNSAT") {
    assert(LazyBasicSolver.solve(FastCongruenceSolver, psi) === false)
  }

  test("larger example SAT") {
    assert(LazyBasicSolver.solve(FastCongruenceSolver, And(eqs)) === true)
  }

  test("larger example UNSAT") {
    assert(LazyBasicSolver.solve(FastCongruenceSolver, And(Not(Equals(a, b)) :: eqs)) === false)
  }

  test("explain") {
    val inputEqs = Set(
      Equals(Apply(gVar, h), d),
      Equals(c, d),
      Equals(Apply(gVar, d), a),
      Equals(e, c),
      Equals(e, b),
      Equals(b, h)
    )
    val cc = new CongruenceClosure
    cc.initialize(inputEqs.asInstanceOf[Set[Formula]])
    inputEqs.foreach(cc.merge)
    
    val explanation = cc.explain(a, b)
    val ccSanity = new CongruenceClosure
    ccSanity.initialize(explanation.asInstanceOf[Set[Formula]])
    explanation.foreach(ccSanity.merge)
    assert(ccSanity.areCongruent(a, b))
  }

  test("setTrue conflicts example 1") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Not(Equals(a,c)), Equals(a,b), Equals(b,c)))
    assert(cc1.setTrue(Not(Equals(a,c))) != None)
    assert(cc1.setTrue(Equals(a,b)) != None)
    assert(cc1.setTrue(Equals(b,c)) === None)

    val cc2 = new CongruenceClosure
    cc2.initialize(Set(Not(Equals(a,c)), Equals(a,b), Equals(b,c)))
    assert(cc2.setTrue(Equals(a,b)) != None)
    assert(cc2.setTrue(Not(Equals(a,c))) != None)
    assert(cc2.setTrue(Equals(b,c)) === None)

    val cc3 = new CongruenceClosure
    cc3.initialize(Set(Not(Equals(a,c)), Equals(a,b), Equals(b,c)))
    assert(cc3.setTrue(Equals(a,b)) != None)
    assert(cc3.setTrue(Equals(b,c)) != None)
    assert(cc3.setTrue(Not(Equals(a,c))) === None)
  }
  
  test("setTrue conflicts example 2") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Equals(Apply(gVar,c),a), Equals(Apply(gVar,d),b), Equals(c,d), Not(Equals(a,b))))
    assert(cc1.setTrue(Equals(Apply(gVar,c),a)) != None)
    assert(cc1.setTrue(Equals(Apply(gVar,d),b)) != None)
    assert(cc1.setTrue(Equals(c,d)) != None)
    assert(cc1.setTrue(Not(Equals(a,b))) === None)
    
    val cc2 = new CongruenceClosure
    cc2.initialize(Set(Equals(Apply(gVar,c),a), Equals(Apply(gVar,d),b), Equals(c,d), Not(Equals(a,b))))
    assert(cc2.setTrue(Equals(Apply(gVar,c),a)) != None)
    assert(cc2.setTrue(Equals(Apply(gVar,d),b)) != None)
    assert(cc2.setTrue(Not(Equals(a,b))) != None)
    assert(cc2.setTrue(Equals(c,d)) === None)
  }

  test("setTrue a != a") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Not(Equals(a,a))))
    assert(cc1.setTrue(Not(Equals(a,a))) === None)
  }

  test("setTrue a = a") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Equals(a,a)))
    assert(cc1.setTrue(Equals(a,a)) != None)
  }
}
