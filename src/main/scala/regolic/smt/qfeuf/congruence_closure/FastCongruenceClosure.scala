package regolic.smt.qfeuf 

import regolic.smt.Solver
import regolic.smt.TheorySolver
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer

import regolic.StopWatch

/*
 * Algorithm described in "Fast congruence closure and extensions"
 * by Robert Nieuwenhuis and Albert Oliveras
 * Handle conjunctions of a = b or f(a,b) = c, where a,b and c are
 * constants. A conjunction of literals in the euf can always be rewriten
 * this way. The solver assume the constants are numbered from 0 to N, with N+1
 * different constatns.
 */
class FastCongruenceClosure extends TheorySolver {

  private[this] val pendingMerges: Queue[Either[
                                     Tuple2[Int, Int],
                                     Tuple2[(Int, Int, Int), (Int, Int, Int)]
                                   ]] = Queue()
  private[this] var repr: Array[Int] = null
  private[this] val lookup: Map[(Int, Int), (Int, Int, Int)] = Map()
  private[this] var useList: Array[ListBuffer[(Int, Int, Int)]] = null
  private[this] var classList: Array[ArrayBuffer[Int]] = null

  //initialize the state with the total number of constants
  //constants will then be identified by integer between 0 and 1
  def initialize(nbConstants: Int): Unit = {
    repr = new Array(nbConstants)
    classList = new Array(nbConstants)
    useList = new Array(nbConstants)
  }

  def merge(a: Int, b: Int): Unit = {
    pendingMerges.enqueue(Left((a, b)))
    propagate()
  }
  def merge(a1: Int, a2: Int, a: Int): Unit = {
    val a1Rep = repr(a1)
    val a2Rep = repr(a2)
    lookup.get((a1Rep, a2Rep)) match {
      case Some((b1, b2, b)) => {
        pendingMerges.enqueue(Right((a1, a2, a), (b1, b2, b)))
        propagate()
      }
      case None => {
        lookup += ((a1Rep, a2Rep) -> Right((a1, a2, a)))
        useList(a1Rep).append((a1, a2, a))
        useList(a2Rep).append((a1, a2, a))
      }
    }
  }
  private def propagate(): Unit = {
    while(pendingMerges.nonEmpty) {
      val e = pendingMerges.dequeue()
      
      val toMerge = e match {
        case (Equals(a: Variable, b: Variable), null) => (termToId(a), termToId(b))
        case (Equals(_, a: Variable), Equals(_, b: Variable)) => (termToId(a), termToId(b))
      }
      val (a, b) = if(classList(repr(toMerge._1)).size > classList(repr(toMerge._2)).size){
        toMerge.swap
      } else toMerge

      // merge classes of a and b (a => b)
      if(repr(a) != repr(b)) {

        // trying to merge classes, which are disequal
        if(diseq(repr(a)).exists{case (t,v,_) => {t.isValid && repr(v) == repr(b)}}) {
          // If for some reason, the trigger literal causing this inconsistency
          // is not pushed onto the I-stack, make sure to set the timestamp
          // invalid here.
          // As it stands now, it gets taken care of in backtrack.
          reason = Not(Equals(idToTerm(repr(toMerge._1)), idToTerm(repr(toMerge._2))))
          return None
        }

        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        var i = 0
        val clOldreprA = classList(oldreprA)
        while(i < clOldreprA.size) {
          val c = clOldreprA(i)

          var pLits = posLitList(c)
          var j = 0
          while(j < pLits.size) {
            pLits(j) match {
              case Equals(t1, t2) => {
                val t1Id = termToId(t1); val t2Id = termToId(t2)
                if((repr(t1Id) == oldreprA && repr(t2Id) == repr(b)) ||
                   (repr(t1Id) == repr(b) && repr(t2Id) == oldreprA))
                  tConsequence += pLits(j)
                else ()
              }
              case _ => ()
            }
            j += 1
          }
          undoReprChangeStack(trigger).push((c, oldreprA, repr(b)))
          repr(c) = repr(b)
          classList(repr(b)).append(c)
          i += 1
        }
        classList(oldreprA).clear()

        var p: Node = diseq(oldreprA).first
        var q: Node = null
        while(p != null) {
          p.data match {
            case (t,v,reason1) if t.isValid => {
              // v hasn't changed its repr, because repr(v) must be different
              // from oldreprA, as it's in disequal(oldreprA)
              diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)
              q = p
              q.next = p.next
            }
            case _ => if(q != null) q.next = p.next else diseq(oldreprA).first = p.next
          }
          p = p.next
        }
        //for(d <- diseq(oldreprA)) {
          //d match {
            //case (t,v,reason1) if t.isValid => {
              //diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)
            //}
            //// Removing while iterating possible with ListBuffer
            //case _ => ()
          //}
        //}
        //diseq(oldreprA) = diseq(oldreprA).filter{case (t,_,_) => t.isValid}

        /*
        // TODO classList is empty here
        for(aP <- classList(oldreprA)) {
          tConsequence ++= negLitList(aP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1); val t2Id = termToId(t2)
              diseq(oldreprA).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))}
            }
          }}
        }
        */
        // optimized: 
        //i = 0
        //while(i < clOldreprA.size) {
          //var nLits = negLitList(clOldreprA(i))
          //var j = 0
          //while(j < nLits.size) {
            //nLits(j) match {
              //case Not(Equals(t1, t2)) => {
                //val t1Id = termToId(t1); val t2Id = termToId(t2)
                //if(diseq(oldreprA).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))})
                  //tConsequence += nLits(j)
                //else ()
              //}
              //case _ => ()
            //}
            //j += 1
          //}
          //i += 1
        //}

        /*
        for(bP <- classList(repr(b))) {
          tConsequence ++= negLitList(bP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1); val t2Id = termToId(t2)
              diseq(repr(b)).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))}
            }
          }}
        }
        */

        for(f1 <- useList(oldreprA)) {
          val Equals(Apply(c1, c2),_) = f1

          val c1Id = termToId(c1); val c2Id = termToId(c2)
          val lookedUp = lookup.getOrElse((repr(c1Id), repr(c2Id)), null)
          if(lookedUp != null && lookedUp._1.isValid) {
            undoUseListStack(trigger).push((f1, oldreprA, -1))
            pendingMerges.enqueue((f1, lookedUp._2))
          } else {
            lookup += ((repr(c1Id), repr(c2Id)) -> (currentTimestamp, f1))

            undoUseListStack(trigger).push((f1, oldreprA, repr(b)))
            useList(repr(b)).append(f1)
          }
        }
        useList(oldreprA).clear()
      } // if
    } // while
    Some(tConsequence.toSet)
  }
  
  private def areCongruent(t1: Term, t2: Term): Boolean = {
    normalize(t1) == normalize(t2)
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => {
        if(termToId.contains(c)) idToTerm(repr(termToId(c))) else c
      }
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        if(u1.isInstanceOf[Variable] && u2.isInstanceOf[Variable]) {
          val lookedUp = lookup.getOrElse((termToId(u1), termToId(u2)), null)
          if(lookedUp != null && lookedUp._1.isValid) {
            val Equals(_, a) = lookedUp._2
            if(termToId.contains(a)) idToTerm(repr(termToId(a))) else a
          } else {
            Apply(u1, u2)
          }
        }
        else
          Apply(u1, u2)
        }
    }
  }

}
