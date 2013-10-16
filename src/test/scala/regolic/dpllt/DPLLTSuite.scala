package regolic.dpllt

import regolic.asts.theories.int.Trees.IntSort
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Apply
import regolic.smt.qfeuf.CongruenceClosure
import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier
//import regolic.smt.qfeuf.FastCongruenceSolver

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
    //println("theory: "+ encoding.theory.mkString("\n", "\n", "\n"))
    //println("theoryOrig: "+ encoding.theoryOrig.mkString("\n", "\n", "\n"))
    //println("constraints: "+ constraints.mkString("\n", "\n", "\n"))
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
    val result = DPLLTSolverWrapper(new CongruenceClosure, phi) match {
      case Results.Satisfiable(_) => true
      case _ => false
    }
    assert(result)
  }

  test("small example UNSAT") {
    assert(DPLLTSolverWrapper(new CongruenceClosure, psi) === Results.Unsatisfiable)
  }

  test("larger example SAT") {
    val result = DPLLTSolverWrapper(new CongruenceClosure, And(eqs)) match {
      case Results.Satisfiable(_) => true
      case _ => false
    }
    assert(result)
  }

  test("larger example UNSAT") {
    assert(DPLLTSolverWrapper(new CongruenceClosure, And(Not(Equals(a, b)) :: eqs)) === Results.Unsatisfiable)
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
    inputEqs.foreach(cc.setTrue)
    
    // fix for not returning functions in the explanation
    val explanation = (cc.explain(Equals(a, b)) + Equals(Apply(gVar, h), d) + Equals(Apply(gVar, d), a))
      
    val ccSanity = new CongruenceClosure
    ccSanity.initialize(explanation.asInstanceOf[Set[Formula]])
    explanation.foreach(ccSanity.setTrue)
    assert(ccSanity.isTrue(Equals(a, b)))
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
    val x4 = freshVariable("x", IntSort());

    // This model is invalid. Either (x3=y3 and y3=x4) or (x3=z3 and z3=x4) has
    // to be true, otherwise the instance is unsat propositionally
    val diamond: List[Formula] = List(
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
      Not(Equals(x3, x4)),
      Equals(x0, x4)
    )
    val cc = new CongruenceClosure
    cc.initialize(diamond.toSet)
    val results = diamond.map(eq => cc.setTrue(eq))
    assert(results.exists(_ == None))
  }


  test("diamond 2") {
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

    val diamond = List[Formula](
      Equals(x0, y0),
      Equals(y0, x1),
      Not(Equals(x0, z0)),
      Not(Equals(z0, x1)),
      Not(Equals(x1, y1)),
      Not(Equals(y1, x2)),
      Equals(x1, z1),
      Equals(z1, x2),
      Equals(x2, y2),
      Equals(y2, x3),
      Not(Equals(x2, z2)),
      Not(Equals(z2, x3)),
      Equals(x3, y3),
      Equals(y3, x4),
      Equals(x3, z3),
      Equals(z3, x4),
      Equals(x4, y4),
      Equals(y4, x5),
      Equals(x4, z4),
      Equals(z4, x5),
      Not(Equals(x5, y5)),
      Not(Equals(y5, x6)),
      Equals(x5, z5),
      Equals(z5, x6),
      Equals(x6, y6),
      Equals(y6, x7),
      Not(Equals(x6, z6)),
      Not(Equals(z6, x7)),
      Not(Equals(x7, y7)),
      Not(Equals(y7, x8)),
      Equals(x7, z7),
      Equals(z7, x8),
      Equals(x8, y8),
      Equals(y8, x9),
      Not(Equals(x8, z8)),
      Not(Equals(z8, x9)),
      Equals(x9, y9),
      Equals(y9, x10),
      Equals(x9, z9),
      Equals(z9, x10),
      Not(Equals(x10, y10)),
      Not(Equals(y10, x11)),
      Equals(x10, z10),
      Equals(z10, x11),
      Equals(x11, y11),
      Equals(y11, x12),
      Not(Equals(x11, z11)),
      Not(Equals(z11, x12)),
      Equals(x12, y12),
      Equals(y12, x13),
      Equals(x12, z12),
      Equals(z12, x13),
      Not(Equals(x13, y13)),
      Not(Equals(y13, x14)),
      Equals(x13, z13),
      Equals(z13, x14),
      Equals(x14, y14),
      Equals(y14, x15),
      Not(Equals(x14, z14)),
      Not(Equals(z14, x15)),
      Equals(x15, y15),
      Equals(y15, x16),
      Equals(x15, z15),
      Equals(z15, x16),
      Equals(x16, y16),
      Equals(y16, x17),
      Equals(x16, z16),
      Equals(z16, x17),
      Equals(x17, y17),
      Equals(y17, x18),
      Not(Equals(x17, z17)),
      Not(Equals(z17, x18)),
      Equals(x18, y18),
      Equals(y18, x19),
      Not(Equals(x18, z18)),
      Not(Equals(z18, x19)),
      Equals(x19, y19),
      Equals(y19, x20),
      Not(Equals(x19, z19)),
      Not(Equals(z19, x20)),
      Equals(x20, y20),
      Equals(y20, x21),
      Not(Equals(x20, z20)),
      Not(Equals(z20, x21)),
      Not(Equals(x21, y21)),
      Not(Equals(y21, x22)),
      Equals(x21, z21),
      Equals(z21, x22),
      Equals(x22, y22),
      Equals(y22, x23),
      Equals(x22, z22),
      Equals(z22, x23),
      Equals(x23, y23),
      Equals(y23, x24),
      Not(Equals(x23, z23)),
      Not(Equals(z23, x24)),
      Not(Equals(x24, y24)),
      Not(Equals(y24, x25)),
      Equals(x24, z24),
      Equals(z24, x25),
      Equals(x25, y25),
      Equals(y25, x26),
      Equals(x25, z25),
      Equals(z25, x26),
      Not(Equals(x0, x26))
    )

    val cc = new CongruenceClosure
    cc.initialize(diamond.toSet)
    val results = diamond.map(eq => cc.setTrue(eq))
    assert(results.reverse.tail.forall(_ != None))
    assert(results.reverse.head == None)
  }

  test("backtrack 3") {
    val eq = Equals(a,b)
    val cc = new CongruenceClosure
    cc.initialize(Set[Formula](eq))
    assert(cc.isTrue(eq) === false)
    cc.setTrue(eq)
    assert(cc.isTrue(eq) === true)
    cc.backtrack(1)
    assert(cc.isTrue(eq) === false)
  }

  test("backtrack 4") {
    val x0 = freshVariable("x", IntSort());
    val x1 = freshVariable("x", IntSort());
    val y0 = freshVariable("y", IntSort());

    val diamond = List[Formula](
      Not(Equals(x0, x1)),
      Equals(x0, y0),
      Equals(y0, x1)
    )

    val afterBacktracking = List[Formula](
      Equals(x0, x1)
    )

    val cc = new CongruenceClosure
    val dSet = diamond.toSet
    cc.initialize(dSet)
    val results = diamond.map(eq => cc.setTrue(eq))
    assert(results.reverse.tail.forall(_ != None))
    assert(results.reverse.head == None)

    cc.backtrack(2)

    val resultsAfterBacktracking = afterBacktracking.map(eq => cc.setTrue(eq))
    assert(resultsAfterBacktracking.exists(_ == None))
            
  }
}

