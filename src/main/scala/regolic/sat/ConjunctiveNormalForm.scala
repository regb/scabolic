package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._

object ConjunctiveNormalForm {

  def apply(formula: Formula): (Set[Set[Literal]], Int, Map[PredicateApplication, Int]) = {
    import scala.collection.mutable.HashMap
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]
    var varToLiteral = new HashMap[PredicateApplication, Int]()

    var literalCounter = -1
    def nextId(): Int = {
      literalCounter += 1
      literalCounter
    }

    //for each subformula, create a new representation and add the constraints while returning the representation
    def rec(form: Formula): Int = form match {
      case Not(f) => {
        val fRepr = rec(f)
        val repr = nextId()
        constraints += Set(new Literal(repr, false), new Literal(fRepr, false))
        constraints += Set(new Literal(repr, true), new Literal(fRepr, true))
        repr
      }
      case And(fs) => {
        val repr = nextId()
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new Literal(repr, false), new Literal(fRepr, true))
        constraints += (new Literal(repr, true) :: fsRepr.map(fRepr => new Literal(fRepr, false))).toSet
        repr
      }
      case Or(fs) => {
        val repr = nextId()
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(new Literal(repr, true), new Literal(fRepr, false))
        constraints += (new Literal(repr, false) :: fsRepr.map(fRepr => new Literal(fRepr, true))).toSet
        repr
      }
      //case Implies(f1, f2) => {
      //  val repr = freshPropositionalVariable("P")
      //  val id = nextId()
      //  varToLiteral(repr) = id
      //  constraints += Or(Not(repr), Not(f1), f2)
      //  constraints += Or(repr, f1)
      //  constraints += Or(repr, Not(f2))
      //  repr
      //}
      //case Iff(f1, f2) => {
      //  val repr = freshPropositionalVariable("P")
      //  val id = nextId()
      //  varToLiteral(repr) = id
      //  constraints += Or(Not(repr), Not(f1), f2)
      //  constraints += Or(Not(repr), f1, Not(f2))
      //  constraints += Or(repr, Not(f1), Not(f2))
      //  constraints += Or(repr, f1, f2)
      //  repr
      //}
      case p@PropositionalVariable(_) => varToLiteral.get(p) match {
        case Some(repr) => repr
        case None => {
          val repr = nextId()
          varToLiteral(p) = repr
          repr
        }
      }
      case _ => sys.error("Unhandled case in ConjunctiveNormalForm: " + form)
    }

    val repr = rec(formula)
    constraints += Set(new Literal(repr, true))
     
    (constraints.toSet, literalCounter + 1, varToLiteral.toMap)
  }

}
