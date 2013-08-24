package regolic.dpllt

import regolic.sat.Literal
import regolic.sat.TLiteral
import regolic.sat.PropLiteral
import regolic.sat.TLiteralID
import regolic.sat.PropLiteralID

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier
import regolic.parsers.SmtLib2.Trees._

import scala.collection.mutable.Map
import scala.collection.mutable.ArrayBuffer

class TheoryPropLiteralEquivalence {
  val encoding = Map[Formula, Int]()
  // in cases where there are no transformations to the literals,
  // theory == theoryOrig
  val theory = new ArrayBuffer[Formula]()
  val theoryOrig = new ArrayBuffer[Formula]()

  def setEquiv(id: Int, f: Formula, fOrig: Formula) {
    // Invariant, id is the amount of calls to setEquiv
    encoding(f) = id
    theory += f
    theoryOrig += fOrig
  }

  def get(f: Formula) = {
    encoding.get(f)
  }
}

object PropositionalSkeleton {

  def apply(formula: Formula, logic: Logic = Undef): (Set[Set[Literal]], TheoryPropLiteralEquivalence) = {
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]

    val tpEquivalence = new TheoryPropLiteralEquivalence

    // For each subformula, create a new representation and add the constraints
    // while returning the representation
    def rec(form: Formula): Int = form match {
      case f@Not((origEq@Equals(_, _))) => {
        // Treat negated equations separately to maintain NNF through flatten
        // transformation
        val ineq :: eqs = Flattener(Currifier(origEq))
        val ineqRepr = tpEquivalence.get(ineq) match {
          case Some(repr) => repr
          case None => {
            val repr = TLiteralID.next
            tpEquivalence.setEquiv(repr, ineq, origEq) 
            repr
          }
        }

      val notRepr = PropLiteralID.next
        constraints += Set(new PropLiteral(notRepr, false), new TLiteral(ineqRepr, false))
        constraints += Set(new PropLiteral(notRepr, true), new TLiteral(ineqRepr, true))
        
        val fsRepr = notRepr :: eqs.map(eq => 
          tpEquivalence.get(eq) match {
            case Some(repr) => repr
            case None => {
              val repr = TLiteralID.next
              tpEquivalence.setEquiv(repr, eq, origEq) 
              repr
            }
          }
        )

        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = PropLiteralID.next
          for(fRepr <- fsRepr)
            constraints += Set(new PropLiteral(andRepr, false), new TLiteral(fRepr, true))
          constraints += (new PropLiteral(andRepr, true) :: fsRepr.map(fRepr => new TLiteral(fRepr, false))).toSet
          andRepr
        } else {
          fsRepr.head
        }
        repr
      }
      case (f: PredicateApplication) => {
        val transformed = logic match {
          case QF_UF => Flattener(Currifier(f))
          case Undef => List(f)
          case _ => throw new Exception("This type of literal hasn't been implemented yet")
        }
        val fsRepr = transformed.map(eq => 
          tpEquivalence.get(eq) match {
            case Some(repr) => repr
            case None => {
              val repr = TLiteralID.next
              tpEquivalence.setEquiv(repr, eq, f) 
              repr
            }
          }
        )
        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = PropLiteralID.next
          for(fRepr <- fsRepr)
            constraints += Set(new PropLiteral(andRepr, false), new TLiteral(fRepr, true))
          constraints += (new PropLiteral(andRepr, true) :: fsRepr.map(fRepr => new TLiteral(fRepr, false))).toSet
          andRepr
        } else {
          fsRepr.head
        }
        repr
      }
      case Not(f) => {
        val fRepr = rec(f)
        val repr = PropLiteralID.next
        constraints += Set(new PropLiteral(repr, false), new Literal(fRepr, false))
        constraints += Set(new PropLiteral(repr, true), new Literal(fRepr, true))
        repr
      }
      case And(fs) => {
        val repr = PropLiteralID.next
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new PropLiteral(repr, false), new Literal(fRepr, true))
        constraints += (new PropLiteral(repr, true) :: fsRepr.map(fRepr => new Literal(fRepr, false))).toSet
        repr
      }
      case Or(fs) => {
        val repr = PropLiteralID.next
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new PropLiteral(repr, true), new Literal(fRepr, false))
        constraints += (new PropLiteral(repr, false) :: fsRepr.map(fRepr => new Literal(fRepr, true))).toSet
        repr
      }
      case Implies(f1, f2) => {
        val repr = PropLiteralID.next
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new PropLiteral(repr, false), new Literal(f1Repr, false), new Literal(f2Repr, true))
        constraints += Set(new PropLiteral(repr, true), new Literal(f1Repr, true))
        constraints += Set(new PropLiteral(repr, true), new Literal(f2Repr, false))
        repr
      }
      case Iff(f1, f2) => {
        val repr = PropLiteralID.next
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new PropLiteral(repr, false), new Literal(f1Repr, false), new Literal(f2Repr, true))
        constraints += Set(new PropLiteral(repr, false), new Literal(f1Repr, true), new Literal(f2Repr, false))
        constraints += Set(new PropLiteral(repr, true), new Literal(f1Repr, false), new Literal(f2Repr, false))
        constraints += Set(new PropLiteral(repr, true), new Literal(f1Repr, true), new Literal(f2Repr, true))
        repr
      }
      case _ => sys.error("Unhandled case in PropositionalSkeleton: " + form)
    }

    val repr = rec(formula)
    constraints += Set(new Literal(repr, true))
     
    (constraints.toSet, tpEquivalence)
  }

}

