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
class FastCongruenceClosure {

  import FastCongruenceClosure._

  private[this] val pendingMerges: Queue[Either[
                                     Tuple2[Int, Int],
                                     Tuple2[(Int, Int, Int), (Int, Int, Int)]
                                   ]] = Queue()
  private[this] var repr: Array[Int] = null
  private[this] val lookup: Map[(Int, Int), (Int, Int, Int)] = Map()
  private[this] var useList: Array[ListBuffer[(Int, Int, Int)]] = null
  private[this] var classList: Array[ListBuffer[Int]] = null

  //initialize the state with the total number of constants
  //constants will then be identified by integer between 0 and 1
  def initialize(nbConstants: Int): Unit = {
    repr = (0 until nbConstants).toArray
    classList = (0 until nbConstants).map(c => {
      val list = new ListBuffer[Int]
      list.append(c)
      list
    }).toArray
    useList = Array.fill(nbConstants)(new ListBuffer)
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
        lookup += ((a1Rep, a2Rep) -> (a1, a2, a))
        useList(a1Rep).append((a1, a2, a))
        useList(a2Rep).append((a1, a2, a))
      }
    }
  }
  private def propagate(): Unit = {
    while(pendingMerges.nonEmpty) {
      val e = pendingMerges.dequeue()
      
      val (aTmp, bTmp) = e match {
        case Left((a, b)) => (a, b)
        case Right(((_, _, a), (_, _, b))) => (a, b)
      }
      val (a, b) = 
        if(classList(repr(aTmp)).size > classList(repr(bTmp)).size)
          (bTmp, aTmp)
        else 
          (aTmp, bTmp)

      val aRep = repr(a)
      val bRep = repr(b)

      if(aRep != bRep) {
        val oldReprA = aRep
        classList(oldReprA).foreach(c => {
          repr(c) = bRep
          classList(bRep).append(c)
        })
        classList(oldReprA).clear()

        useList(oldReprA).foreach{case f1@(c1, c2, c) => {
          lookup.get((repr(c1), repr(c2))) match {
            case Some((d1, d2, d)) => {
              pendingMerges.enqueue(Right(((c1, c2, c), (d1, d2, d))))
            }
            case None => {
              lookup += ((repr(c1), repr(c2)) -> f1)
              useList(bRep).append(f1)
            }
          }
        }}
        useList(oldReprA).clear()
      }
    }
  }
  
  def areCongruent(t1: ApplyConstantTerms, t2: ApplyConstantTerms): Boolean = {
    normalize(t1) == normalize(t2)
  }

  private def normalize(t: ApplyConstantTerms): ApplyConstantTerms = t match {
    case Constant(c) => Constant(repr(c))
    case Apply(t1, t2) => {
      val u1 = normalize(t1)
      val u2 = normalize(t2)
      (u1, u2) match {
        case (Constant(c1), Constant(c2)) => lookup.get((c1, c2)) match {
          case Some((_, _, a)) => Constant(repr(a))
          case None => Apply(u1, u2)
        }
        case _ => Apply(u1, u2)
      }
    }
  }

}

object FastCongruenceClosure {
  sealed trait ApplyConstantTerms
  case class Constant(c: Int) extends ApplyConstantTerms
  case class Apply(t1: ApplyConstantTerms, t2: ApplyConstantTerms) extends ApplyConstantTerms
}
