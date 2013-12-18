//package regolic
//package dpllt
//package qfa
//
//import regolic.asts.core.Trees._
//import regolic.asts.core.Manip._
//import regolic.asts.fol.Trees._
//import regolic.asts.fol.Manip._
//import regolic.asts.theories.array.Trees._
//
//import scala.collection.mutable.HashMap
//import scala.collection.mutable.ListBuffer
//
//class Component(implicit val context: Context) extends TheoryComponent {
//
//  case class Literal(lhs: Term, rhs: Term, id: Int, polInt: Int) extends AbstractLiteral
//
//
//  class Solver extends AbstractSolver {
//
//    override def setTrue(l: Literal): Either[Set[Literal], Set[Literal]]
//
//
//    def isSat(and: List[Formula]): Option[Map[FunctionSymbol, Term]] = {
//
//      def isReadOverWrite(t: Term): Boolean = t match {
//        case Select(Store(a, i, v), j) => true
//        case _ => false
//      }
//
//      var additionalCnstr: Formula = null
//      val (And(newLits), found) = findAndMap(And(and), (f: Formula) => false, isReadOverWrite _, (f: Formula) => f, (t: Term) => {
//        val Select(Store(a, i, v), j) = t
//        additionalCnstr = Equals(i, j)
//        v
//      })
//
//      if(!found) {
//        isSatNoStore(and)
//      } else {
//        isSat(additionalCnstr :: newLits) match {
//          case Some(m) => Some(m)
//          case None => {
//            val (And(newLits), _) = findAndMap(And(and), (f: Formula) => false, isReadOverWrite _, (f: Formula) => f, (t: Term) => {
//              val Select(Store(a, i, v), j) = t
//              additionalCnstr = Not(Equals(i, j))
//              Select(a, j)
//            })
//            isSat(additionalCnstr :: newLits)
//          }
//        }
//      }
//    }
//
//  // TODO signature and FastCongruenceSolver
//  //the clause only contains select or top level store that can be safely eliminated
//  private def isSatNoStore(and: List[Formula]): Option[Map[FunctionSymbol, Term]] = {
//    var arrayVarToFun: Map[FunctionSymbol, FunctionSymbol] = Map()
//    def removeStore(t: Term): Term = t match {
//      case Store(a, _, _) => a
//      case sel@Select(FunctionApplication(a: FunctionSymbol, List()), i) => arrayVarToFun.get(a) match {
//        case Some(f) => FunctionApplication(f, List(i))
//        case None => {
//          val f = freshFunctionSymbol("f", List(i.sort), sel.sort)
//          arrayVarToFun += (a -> f)
//          FunctionApplication(f, List(i))
//        }
//      }
//      case t => t
//    }
//    val And(cleanTerms) = mapPreorder(And(and), (f: Formula) => f, removeStore _)
//    regolic.smt.qfeuf.CongruenceSolver.isSat(cleanTerms)
//  }
//
//}
