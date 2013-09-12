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

import org.scalatest.FunSuite

class DPLLTSuite extends FunSuite {

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

    val (constraints, encoding, _, _) = PropositionalSkeleton(f)
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

  test("backtrack 1") {
    // (a=b) AND (d=e OR a!=c) AND (b=c)
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Equals(a,b), Equals(d,e), Equals(a,c), Not(Equals(b,c))))
    assert(cc1.setTrue(Equals(a,b)) != None)
    assert(cc1.setTrue(Not(Equals(a,c))) != None)
    assert(cc1.setTrue(Equals(b,c)) === None)
    cc1.backtrack(2)
    assert(cc1.setTrue(Equals(d,e)) != None)
    assert(cc1.setTrue(Equals(b,c)) != None)
  }

  test("backtrack 2") {
    val cc1 = new CongruenceClosure
    cc1.initialize(Set(Equals(Apply(gVar,e),b), Equals(d,a),
      Not(Equals(h,c)), Equals(Apply(gVar,h),b),
      Equals(Apply(gVar,h),c), Equals(Apply(gVar,e),h)))
    assert(cc1.setTrue(Equals(Apply(gVar,e),b)) != None)
    assert(cc1.setTrue(Equals(Apply(gVar,e),h)) != None)
    assert(cc1.setTrue(Equals(Apply(gVar,h),b)) != None)
    assert(cc1.setTrue(Equals(Apply(gVar,h),c)) != None)
    assert(cc1.setTrue(Not(Equals(h,c))) === None)
    cc1.backtrack(1)
    assert(cc1.setTrue(Equals(d,a)) != None)
  }

  // (assert (= (f (f x)) x))
  // (assert (= (f x) y))
  // (assert (not (= x y)))
  test("nested functions") {
    val cc1 = new CongruenceClosure
    val l1 = Flattener(Currifier(
      Equals(FunctionApplication(g, List(FunctionApplication(g, List(x)))), x)
    ))

    val l2 = Flattener(Currifier(
      Equals(FunctionApplication(g, List(x)),y)
    ))

    val eqs: Set[Formula] = (l1 ::: l2).toSet + Not(Equals(x,y))
    cc1.initialize(eqs)
    eqs.foreach(eq => assert(cc1.setTrue(eq) != None))
  }

  test("diamond") {
    val x0 = freshVariable("x", IntSort()); val y0 = freshVariable("y", IntSort()); val z0 = freshVariable("z", IntSort());
    val x1 = freshVariable("x", IntSort()); val y1 = freshVariable("y", IntSort()); val z1 = freshVariable("z", IntSort());
    val x2 = freshVariable("x", IntSort()); val y2 = freshVariable("y", IntSort()); val z2 = freshVariable("z", IntSort());
    val x3 = freshVariable("x", IntSort()); val y3 = freshVariable("y", IntSort()); val z3 = freshVariable("z", IntSort());
    val x4 = freshVariable("x", IntSort()); val y4 = freshVariable("y", IntSort()); val z4 = freshVariable("z", IntSort());
    val x5 = freshVariable("x", IntSort()); val y5 = freshVariable("y", IntSort()); val z5 = freshVariable("z", IntSort());
    val x6 = freshVariable("x", IntSort()); val y6 = freshVariable("y", IntSort()); val z6 = freshVariable("z", IntSort());
    val x7 = freshVariable("x", IntSort()); val y7 = freshVariable("y", IntSort()); val z7 = freshVariable("z", IntSort());
    val x8 = freshVariable("x", IntSort()); val y8 = freshVariable("y", IntSort()); val z8 = freshVariable("z", IntSort());
    val x9 = freshVariable("x", IntSort()); val y9 = freshVariable("y", IntSort()); val z9 = freshVariable("z", IntSort());
    val x10 = freshVariable("x", IntSort()); val y10 = freshVariable("y", IntSort()); val z10 = freshVariable("z", IntSort());
    val x11 = freshVariable("x", IntSort()); val y11 = freshVariable("y", IntSort()); val z11 = freshVariable("z", IntSort());
    val x12 = freshVariable("x", IntSort()); val y12 = freshVariable("y", IntSort()); val z12 = freshVariable("z", IntSort());
    val x13 = freshVariable("x", IntSort()); val y13 = freshVariable("y", IntSort()); val z13 = freshVariable("z", IntSort());
    val x14 = freshVariable("x", IntSort()); val y14 = freshVariable("y", IntSort()); val z14 = freshVariable("z", IntSort());
    val x15 = freshVariable("x", IntSort()); val y15 = freshVariable("y", IntSort()); val z15 = freshVariable("z", IntSort());
    val x16 = freshVariable("x", IntSort()); val y16 = freshVariable("y", IntSort()); val z16 = freshVariable("z", IntSort());
    val x17 = freshVariable("x", IntSort()); val y17 = freshVariable("y", IntSort()); val z17 = freshVariable("z", IntSort());
    val x18 = freshVariable("x", IntSort()); val y18 = freshVariable("y", IntSort()); val z18 = freshVariable("z", IntSort());
    val x19 = freshVariable("x", IntSort()); val y19 = freshVariable("y", IntSort()); val z19 = freshVariable("z", IntSort());
    val x20 = freshVariable("x", IntSort()); val y20 = freshVariable("y", IntSort()); val z20 = freshVariable("z", IntSort());
    val x21 = freshVariable("x", IntSort()); val y21 = freshVariable("y", IntSort()); val z21 = freshVariable("z", IntSort());
    val x22 = freshVariable("x", IntSort()); val y22 = freshVariable("y", IntSort()); val z22 = freshVariable("z", IntSort());
    val x23 = freshVariable("x", IntSort()); val y23 = freshVariable("y", IntSort()); val z23 = freshVariable("z", IntSort());
    val x24 = freshVariable("x", IntSort()); val y24 = freshVariable("y", IntSort()); val z24 = freshVariable("z", IntSort());
    val x25 = freshVariable("x", IntSort()); val y25 = freshVariable("y", IntSort()); val z25 = freshVariable("z", IntSort());
    val x26 = freshVariable("x", IntSort()); val y26 = freshVariable("y", IntSort()); val z26 = freshVariable("z", IntSort());

    val diamond: Set[Formula] = Set(
      Not(Equals(x0, y0)),
      Not(Equals(y0, x1)),
      Equals(x0, z0),
      Equals(z0, x1),
      Equals(x1, y1),
      Equals(y1, x2),
      Not(Equals(x1, z1)),
      Not(Equals(z1, x2)),
      Not(Equals(x2, y2)),
      Not(Equals(y2, x3)),
      Equals(x2, z2),
      Equals(z2, x3),
      Not(Equals(x3, y3)),
      Not(Equals(y3, x4)),
      Not(Equals(x3, z3)),
      Not(Equals(z3, x4)),
      Not(Equals(x4, y4)),
      Not(Equals(y4, x5)),
      Not(Equals(x4, z4)),
      Not(Equals(z4, x5)),
      Equals(x5, y5),
      Equals(y5, x6),
      Not(Equals(x5, z5)),
      Not(Equals(z5, x6)),
      Not(Equals(x6, y6)),
      Not(Equals(y6, x7)),
      Equals(x6, z6),
      Equals(z6, x7),
      Equals(x7, y7),
      Equals(y7, x8),
      Not(Equals(x7, z7)),
      Not(Equals(z7, x8)),
      Not(Equals(x8, y8)),
      Not(Equals(y8, x9)),
      Equals(x8, z8),
      Equals(z8, x9),
      Not(Equals(x9, y9)),
      Not(Equals(y9, x10)),
      Not(Equals(x9, z9)),
      Not(Equals(z9, x10)),
      Equals(x10, y10),
      Equals(y10, x11),
      Not(Equals(x10, z10)),
      Not(Equals(z10, x11)),
      Not(Equals(x11, y11)),
      Not(Equals(y11, x12)),
      Equals(x11, z11),
      Equals(z11, x12),
      Not(Equals(x12, y12)),
      Not(Equals(y12, x13)),
      Not(Equals(x12, z12)),
      Not(Equals(z12, x13)),
      Equals(x13, y13),
      Equals(y13, x14),
      Not(Equals(x13, z13)),
      Not(Equals(z13, x14)),
      Not(Equals(x14, y14)),
      Not(Equals(y14, x15)),
      Equals(x14, z14),
      Equals(z14, x15),
      Not(Equals(x15, y15)),
      Not(Equals(y15, x16)),
      Not(Equals(x15, z15)),
      Not(Equals(z15, x16)),
      Not(Equals(x16, y16)),
      Not(Equals(y16, x17)),
      Not(Equals(x16, z16)),
      Not(Equals(z16, x17)),
      Not(Equals(x17, y17)),
      Not(Equals(y17, x18)),
      Equals(x17, z17),
      Equals(z17, x18),
      Not(Equals(x18, y18)),
      Not(Equals(y18, x19)),
      Equals(x18, z18),
      Equals(z18, x19),
      Not(Equals(x19, y19)),
      Not(Equals(y19, x20)),
      Equals(x19, z19),
      Equals(z19, x20),
      Not(Equals(x20, y20)),
      Not(Equals(y20, x21)),
      Equals(x20, z20),
      Equals(z20, x21),
      Equals(x21, y21),
      Equals(y21, x22),
      Not(Equals(x21, z21)),
      Not(Equals(z21, x22)),
      Not(Equals(x22, y22)),
      Not(Equals(y22, x23)),
      Not(Equals(x22, z22)),
      Not(Equals(z22, x23)),
      Not(Equals(x23, y23)),
      Not(Equals(y23, x24)),
      Equals(x23, z23),
      Equals(z23, x24),
      Equals(x24, y24),
      Equals(y24, x25),
      Not(Equals(x24, z24)),
      Not(Equals(z24, x25)),
      Not(Equals(x25, y25)),
      Not(Equals(y25, x26)),
      Not(Equals(x25, z25)),
      Not(Equals(z25, x26)),
      Equals(x0, x26)
    )
    val cc = new CongruenceClosure
    cc.initialize(diamond)
    val results = diamond.map(eq => cc.setTrue(eq))
    assert(results.exists(_ == None))
    assert(regolic.smt.qfeuf.CongruenceSolver.isSat(diamond.toList) == None)
  }
}
