package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._

object ConjunctiveNormalForm {

  def apply(formula: Formula): (Set[Set[Literal]], Int, Map[Formula, Int]) = {
    import scala.collection.mutable.HashMap
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]
    var varToPropLiteral = new HashMap[Formula, Int]()

    //for each subformula, create a new representation and add the constraints while returning the representation
    def rec(form: Formula): Int = form match {
      case Not(f) => {
        val fRepr = rec(f)
        val repr = PropLiteralID.next
        constraints += Set(new PropLiteral(repr, false), new PropLiteral(fRepr, false))
        constraints += Set(new PropLiteral(repr, true), new PropLiteral(fRepr, true))
        repr
      }
      case And(fs) => {
        val repr = PropLiteralID.next
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new PropLiteral(repr, false), new PropLiteral(fRepr, true))
        constraints += (new PropLiteral(repr, true) :: fsRepr.map(fRepr => new PropLiteral(fRepr, false))).toSet
        repr
      }
      case Or(fs) => {
        val repr = PropLiteralID.next
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new PropLiteral(repr, true), new PropLiteral(fRepr, false))
        constraints += (new PropLiteral(repr, false) :: fsRepr.map(fRepr => new PropLiteral(fRepr, true))).toSet
        repr
      }
      case Implies(f1, f2) => {
        val repr = PropLiteralID.next
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new PropLiteral(repr, false), new PropLiteral(f1Repr, false), new PropLiteral(f2Repr, true))
        constraints += Set(new PropLiteral(repr, true), new PropLiteral(f1Repr, true))
        constraints += Set(new PropLiteral(repr, true), new PropLiteral(f2Repr, false))
        repr
      }
      case Iff(f1, f2) => {
        val repr = PropLiteralID.next
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new PropLiteral(repr, false), new PropLiteral(f1Repr, false), new PropLiteral(f2Repr, true))
        constraints += Set(new PropLiteral(repr, false), new PropLiteral(f1Repr, true), new PropLiteral(f2Repr, false))
        constraints += Set(new PropLiteral(repr, true), new PropLiteral(f1Repr, false), new PropLiteral(f2Repr, false))
        constraints += Set(new PropLiteral(repr, true), new PropLiteral(f1Repr, true), new PropLiteral(f2Repr, true))
        repr
      }
      case p@PropositionalVariable(_) => varToPropLiteral.get(p) match {
        case Some(repr) => repr
        case None => {
          val repr = PropLiteralID.next
          varToPropLiteral(p) = repr
          repr
        }
      }
      case _ => sys.error("Unhandled case in ConjunctiveNormalForm: " + form)
    }

    val repr = rec(formula)
    constraints += Set(new PropLiteral(repr, true))
     
    (constraints.toSet, PropLiteralID.count, varToPropLiteral.toMap)
  }

}
