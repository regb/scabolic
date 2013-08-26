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

class Encoding {
  val id = Map[Formula, Int]()
  // in cases where there are no transformations to the literals,
  // theory == theoryOrig
  val theory = new ArrayBuffer[Formula]()
  val theoryOrig = new ArrayBuffer[Formula]()

  def setEquiv(id: Int, f: Formula, fOrig: Formula) {
    // Invariant, id is the amount of calls to setEquiv
    this.id(f) = id
    theory += f
    theoryOrig += fOrig
  }

  def get(f: Formula) = {
    this.id.get(f)
  }
}

object PropositionalSkeleton {

  def apply(formula: Formula, logic: Logic = Undef): (Set[Set[Literal]], Encoding) = {
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]

    val encoding = new Encoding

    // For each subformula, create a new representation and add the constraints
    // while returning the representation
    def rec(form: Formula): Literal = form match {
      case f@Not((origEq@Equals(_, _))) => {
        // Treat negated equations separately to maintain NNF through flatten
        // transformation
        val ineq :: eqs = Flattener(Currifier(origEq))
        val ineqRepr = encoding.get(ineq) match {
          case Some(repr) => new TLiteral(repr)
          case None => {
            val reprID = TLiteralID.next
            encoding.setEquiv(reprID, ineq, origEq) 
            new TLiteral(reprID)
          }
        }

        val notRepr = new PropLiteral(PropLiteralID.next)
        constraints += Set(notRepr.neg, ineqRepr.neg)
        constraints += Set(notRepr.pos, ineqRepr.pos)
        
        val fsRepr = notRepr :: eqs.map(eq => 
          encoding.get(eq) match {
            case Some(repr) => new TLiteral(repr)
            case None => {
              val reprID = TLiteralID.next
              encoding.setEquiv(reprID, eq, origEq) 
              new TLiteral(reprID)
            }
          }
        )

        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = new PropLiteral(PropLiteralID.next)
          for(fRepr <- fsRepr)
            constraints += Set(andRepr.neg, fRepr.pos)
          constraints += (andRepr.pos :: fsRepr.map(fRepr => fRepr.neg)).toSet
          andRepr
        } else {
          fsRepr.head
        }
        repr
      }
      case (f: PredicateApplication) => {
        val fsRepr = logic match {
          case QF_UF => Flattener(Currifier(f)).map(eq => 
            encoding.get(eq) match {
              case Some(repr) => new TLiteral(repr)
              case None => {
                val repr = TLiteralID.next
                encoding.setEquiv(repr, eq, f) 
                new TLiteral(repr)
              }
            }
          )
          case Undef => {
            val reprID = PropLiteralID.next
            // TODO vartoliteral(reprID) = f
            List(new PropLiteral(reprID))
          }
          case _ => throw new Exception("This type of literal hasn't been implemented yet")
        }
        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = new PropLiteral(PropLiteralID.next)
          for(fRepr <- fsRepr)
            constraints += Set(andRepr.neg, fRepr.pos)
          constraints += (andRepr.pos :: fsRepr.map(fRepr => fRepr.neg)).toSet
          andRepr
        } else {
          fsRepr.head
        }
        repr
      }
      case Not(f) => {
        val fRepr = rec(f)
        val repr = new PropLiteral(PropLiteralID.next)
        constraints += Set(repr.neg, fRepr.neg)
        constraints += Set(repr.pos, fRepr.pos)
        repr
      }
      case And(fs) => {
        val repr = new PropLiteral(PropLiteralID.next)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.neg, fRepr.pos)
        constraints += (repr.pos :: fsRepr.map(fRepr => fRepr.neg)).toSet
        repr
      }
      case Or(fs) => {
        val repr = new PropLiteral(PropLiteralID.next)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.pos, fRepr.neg)
        constraints += (repr.neg :: fsRepr.map(fRepr => fRepr.pos)).toSet
        repr
      }
      case Implies(f1, f2) => {
        val repr = new PropLiteral(PropLiteralID.next)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.pos, f1Repr.pos)
        constraints += Set(repr.pos, f2Repr.neg)
        repr
      }
      case Iff(f1, f2) => {
        val repr = new PropLiteral(PropLiteralID.next)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.neg, f1Repr.pos, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.neg, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.pos, f2Repr.pos)
        repr
      }
      case _ => sys.error("Unhandled case in PropositionalSkeleton: " + form)
    }

    val repr = rec(formula)
    constraints += Set(repr.pos)
     
    (constraints.toSet, encoding)
  }

}

