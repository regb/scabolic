package regolic
package dpllt

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import scala.collection.mutable.ArrayBuffer

object PropositionalSkeleton {

  def apply(formula: Formula, builder: (PredicateApplication, Int, Boolean) => Literal): 
    (Set[Set[Literal]], Int, Map[Formula, Literal]) = {
    import scala.collection.mutable.HashMap
    import scala.collection.mutable.ListBuffer

    //TODO: move in some util/common generics class
    trait Counter {
      private var counter = -1
      def next = {
        counter += 1
        counter
      }

      def count = counter + 1

      def reset = {
        counter = -1
      }
    }
    object LiteralId extends Counter

    val constraints = new ListBuffer[Set[Literal]]
    var varToLiteral = new HashMap[Formula, Literal]()

    //for each subformula, create a new representation and add the constraints while returning the representation
    //the representative is always the positive literal
    def rec(form: Formula): Literal = form match {
      case (p: PredicateApplication) => {
        val repr = p match {
          case Equals(_, _) => varToLiteral.get(p) match {
            case Some(repr) => repr
            case None => {
              val repr = builder(p, LiteralId.next, true)
              varToLiteral(p) = repr
              repr
            }
          }
          case p@PropositionalVariable(_) => varToLiteral.get(p) match {
            case Some(repr) => repr
            case None => {
              val repr = new PropositionalLiteral(LiteralId.next, true)
              varToLiteral(p) = repr
              repr
            }
          }
          case _ => throw new Exception("This type of literal hasn't been implemented yet: "+ p)
        }
        repr
      }
      case Not(f) => {
        val fRepr = rec(f)
        val repr = new PropositionalLiteral(LiteralId.next, true)
        constraints += Set(repr.neg, fRepr.neg)
        constraints += Set(repr.pos, fRepr.pos)
        repr
      }
      case And(fs) => {
        val repr = new PropositionalLiteral(LiteralId.next, true)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.neg, fRepr.pos)
        constraints += (repr.pos :: fsRepr.map(fRepr => fRepr.neg)).toSet
        repr
      }
      case Or(fs) => {
        val repr = new PropositionalLiteral(LiteralId.next, true)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.pos, fRepr.neg)
        constraints += (repr.neg :: fsRepr.map(fRepr => fRepr.pos)).toSet
        repr
      }
      case Implies(f1, f2) => {
        val repr = new PropositionalLiteral(LiteralId.next, true)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.pos, f1Repr.pos)
        constraints += Set(repr.pos, f2Repr.neg)
        repr
      }
      case Iff(f1, f2) => {
        val repr = new PropositionalLiteral(LiteralId.next, true)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.neg, f1Repr.pos, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.neg, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.pos, f2Repr.pos)
        repr
      }
      case _ => sys.error("Unhandled case in ConjunctiveNormalForm: " + form)
    }

    val repr = rec(formula)
    constraints += Set(repr)
     
    (constraints.toSet, LiteralId.count, varToLiteral.toMap)
  }

}
