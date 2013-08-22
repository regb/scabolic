package regolic.dpllt

import regolic.sat.Literal
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier
import regolic.parsers.SmtLib2.Trees._

import scala.collection.mutable.HashMap

class TheoryPropLiteralEquivalence {
  var encoding = new HashMap[Formula, Int]()
  // in cases where there are no transformations to the literals,
  // theory == theoryOrig
  var theory = new HashMap[Int, Formula]()
  var theoryOrig = new HashMap[Int, Formula]()

  def setEquiv(id: Int, f: Formula, fOrig: Formula) {
    encoding(f) = id
    theory(id) = f
    theoryOrig(id) = fOrig
  }

  def get(f: Formula) = {
    encoding.get(f)
  }
}

//TODO this subsumes ConjunctiveNormalForm
// figure out how to move it into sat/smt?
object PropositionalSkeleton {

  def apply(formula: Formula, logic: Logic = Undef): (Set[Set[Literal]], Int, TheoryPropLiteralEquivalence) = {
    import scala.collection.mutable.ListBuffer

    val constraints = new ListBuffer[Set[Literal]]

    val tpEquivalence = new TheoryPropLiteralEquivalence

    var literalCounter = -1
    def nextId(): Int = {
      literalCounter += 1
      literalCounter
    }
    
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
            val repr = nextId()
            tpEquivalence.setEquiv(repr, ineq, origEq) 
            repr
          }
        }

        val notRepr = nextId()
        constraints += Set(new Literal(notRepr, false), new Literal(ineqRepr, false))
        constraints += Set(new Literal(notRepr, true), new Literal(ineqRepr, true))
        
        val fsRepr = notRepr :: eqs.map(eq => 
          tpEquivalence.get(eq) match {
            case Some(repr) => repr
            case None => {
              val repr = nextId()
              tpEquivalence.setEquiv(repr, eq, origEq) 
              repr
            }
          }
        )

        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = nextId()
          for(fRepr <- fsRepr)
            constraints += Set(new Literal(andRepr, false), new Literal(fRepr, true))
          constraints += (new Literal(andRepr, true) :: fsRepr.map(fRepr => new Literal(fRepr, false))).toSet
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
              val repr = nextId()
              tpEquivalence.setEquiv(repr, eq, f) 
              repr
            }
          }
        )
        val repr = if(fsRepr.tail != Nil) {
          // AND all the flattened terms together
          val andRepr = nextId()
          for(fRepr <- fsRepr)
            constraints += Set(new Literal(andRepr, false), new Literal(fRepr, true))
          constraints += (new Literal(andRepr, true) :: fsRepr.map(fRepr => new Literal(fRepr, false))).toSet
          andRepr
        } else {
          fsRepr.head
        }
        repr
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
     
    (constraints.toSet, literalCounter + 1, tpEquivalence)
  }

}

//package regolic.dpllt

//import regolic.sat.Literal
//import regolic.asts.core.Trees._
//import regolic.asts.fol.Trees._

//import regolic.smt.qfeuf.Flattener
//import regolic.smt.qfeuf.Currifier
//import regolic.parsers.SmtLib2.Trees._

//class TheoryPropLiteralEquivalence {
  //var encoding = new HashMap[Formula, Int]()
  //// in cases where there are no transformations to the literals,
  //// theory == theoryOrig
  //var theory = new HashMap[Int, Formula]()
  //var theoryOrig = new HashMap[Int, Formula]()

  //def setEquiv(id: Int, f: Formula, fOrig: Formula) {
    //encoding(f) = id
    //theory(id) = f
    //theoryOrig(id) = fOrig
  //}

  //def get(f: Formula) = {
    //encoding.get(f)
  //}
//}

////TODO this subsumes ConjunctiveNormalForm
//// figure out how to move it into sat/smt?
//object PropositionalSkeleton {

  //def apply(formula: Formula, logic: Logic = Undef): (Set[Set[Literal]], Int, TheoryPropLiteralEquivalence) = {
    //import scala.collection.mutable.HashMap
    //import scala.collection.mutable.ListBuffer

    //val constraints = new ListBuffer[Set[Literal]]

    //val tpEquivalence = new TheoryPropLiteralEquivalence

    //var literalCounter = -1
    //def nextId(): Int = {
      //literalCounter += 1
      //literalCounter
    //}
    
    //// For each subformula, create a new representation and add the constraints
    //// while returning the representation
    //def rec(form: Formula): Int = form match {
      //case Not((p: PredicateApplication)) => {
        //val transformed = logic match {
          //case QF_UF => Flattener(Currifier(p))
          //case Undef => p
          //case _ => throw new Exception("This type of literal hasn't been implemented yet")
        //}

        //if(transformed.tail != Nil) {
          //And(Not(transformed.head) :: transformed.tail)
        //} else {
          //Not(transformed)
        //}
      //}
      //case (f: PredicateApplication) => {
        //val transformed = logic match {
          //case QF_UF => Flattener(Currifier(f))
          //case Undef => f
          //case _ => throw new Exception("This type of literal hasn't been implemented yet")
        //}

        //if(transformed.tail != Nil) {
          //And(transformed)
        //} else {
          //transformed
        //}
      //}
      //case Not(f) => {
        //Not(rec(f))
      //}
      //case And(fs) => {
        //And(fs.map(f => rec(f)))
      //}
      //case Or(fs) => {
        //Or(fs.map(f => rec(f)))
      //}
      //case Implies(f1, f2) => {
        //Implies(rec(f1), rec(f2))
      //}
      //case Iff(f1, f2) => {
        //Iff(rec(f1), rec(f2))
      //}
      //case _ => sys.error("Unhandled case in PropositionalSkeleton: " + form)
    //}

    //val repr = rec(formula)
    //constraints += Set(new Literal(repr, true))
     
    //(constraints.toSet, literalCounter + 1, tpEquivalence)
  //}

//}

