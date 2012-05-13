package regolic.smt.qfa

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.asts.theories.array.Trees._

import regolic.parsers.SmtLib2.Trees.QF_A

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

object Solver extends regolic.smt.Solver {

  val logic = QF_A

  def isSat(f: Formula): Option[Map[FunctionSymbol, Term]] = {
    val Or(ands) = disjunctiveNormalForm(f)

    var modelFound = false

    for(And(lits) <- ands if !modelFound) {
      isSat(lits) match {
        case Some(_) => modelFound = true
        case _ => 
      }
    }

    if(modelFound) Some(Map()) else None
  }

  def isSat(and: List[Formula]): Option[Map[FunctionSymbol, Term]] = {

    def isReadOverWrite(t: Term): Boolean = t match {
      case Select(Store(a, i, v), j) => true
      case _ => false
    }

    var additionalCnstr: Formula = null
    println("Before findandmap: " + and)
    val (And(newLits), found) = findAndMap(And(and), (f: Formula) => false, isReadOverWrite _, (f: Formula) => f, (t: Term) => {
      val Select(Store(a, i, v), j) = t
      additionalCnstr = Equals(i, j)
      v
    })
    println("After findandmap: " + newLits)
    println("Found: " + found)

    if(!found) {
      isSatNoStore(and)
    } else {
      isSat(additionalCnstr :: newLits) match {
        case Some(m) => Some(m)
        case None => {
    println("Before findandmap: " + and)
          val (And(newLits), _) = findAndMap(And(and), (f: Formula) => false, isReadOverWrite _, (f: Formula) => f, (t: Term) => {
            val Select(Store(a, i, v), j) = t
            additionalCnstr = Not(Equals(i, j))
            Select(a, j)
          })
    println("After findandmap: " + newLits)
          isSat(additionalCnstr :: newLits)
        }
      }
    }
  }

  //the clause only contains select or top level store that can be safely eliminated
  private def isSatNoStore(and: List[Formula]): Option[Map[FunctionSymbol, Term]] = {
    var arrayVarToFun: Map[FunctionSymbol, FunctionSymbol] = Map()
    def removeStore(t: Term): Term = t match {
      case Store(a, _, _) => a
      case sel@Select(FunctionApplication(a: FunctionSymbol, List()), i) => arrayVarToFun.get(a) match {
        case Some(f) => FunctionApplication(f, List(i))
        case None => {
          val f = freshFunctionSymbol("f", List(i.sort), sel.sort)
          arrayVarToFun += (a -> f)
          FunctionApplication(f, List(i))
        }
      }
      case t => t
    }
    val And(cleanTerms) = mapPreorder(And(and), (f: Formula) => f, removeStore _)
    println("Sending to euf: " + cleanTerms)
    regolic.smt.qfeuf.CongruenceSolver.isSat(cleanTerms)
  }

}