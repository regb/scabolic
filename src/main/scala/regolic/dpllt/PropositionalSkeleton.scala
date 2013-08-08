package regolic.dpllt

import regolic.sat.Literal
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

object PropositionalSkeleton {

  def apply(formula: Formula): (Set[Set[Literal]], Int, Map[Int, Formula],
    Map[Formula, Int]) = {
    import scala.collection.mutable.HashMap
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]
    var theoryLitToId = new HashMap[Formula, Int]()
    var idToTheoryLit = new HashMap[Int, Formula]()

    var literalCounter = -1
    def nextId(): Int = {
      literalCounter += 1
      literalCounter
    }
    
    //for each subformula, create a new representation and add the constraints while returning the representation
    def rec(form: Formula): Int = form match {
      case eq@Equals(_, _) => {
        theoryLitToId.get(eq) match {
          case Some(repr) => repr
          case None => {
            val repr = nextId()
            theoryLitToId(eq) = repr
            idToTheoryLit(repr) = eq
            repr
          }
        }
      }
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
      case Implies(f1, f2) => {
        val repr = nextId()
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new Literal(repr, false), new Literal(f1Repr, false), new Literal(f2Repr, true))
        constraints += Set(new Literal(repr, true), new Literal(f1Repr, true))
        constraints += Set(new Literal(repr, true), new Literal(f2Repr, false))
        repr
      }
      case Iff(f1, f2) => {
        val repr = nextId()
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(new Literal(repr, false), new Literal(f1Repr, false), new Literal(f2Repr, true))
        constraints += Set(new Literal(repr, false), new Literal(f1Repr, true), new Literal(f2Repr, false))
        constraints += Set(new Literal(repr, true), new Literal(f1Repr, false), new Literal(f2Repr, false))
        constraints += Set(new Literal(repr, true), new Literal(f1Repr, true), new Literal(f2Repr, true))
        repr
      }
      case _ => sys.error("Unhandled case in PropositionalSkeleton: " + form)
    }

    val repr = rec(formula)
    constraints += Set(new Literal(repr, true))
     
    (constraints.toSet, literalCounter + 1, idToTheoryLit.toMap, theoryLitToId.toMap)
  }

}

