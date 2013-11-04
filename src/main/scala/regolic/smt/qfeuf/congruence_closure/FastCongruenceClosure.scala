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

  type InputEquation = Either[(Int, Int), (Int, Int, Int)]
  type MergePair = Either[
                     Tuple2[Int, Int],
                     Tuple2[(Int, Int, Int), (Int, Int, Int)]
                   ]

  private[this] var nbConstants = 0

  private[this] val pendingMerges: Queue[MergePair] = Queue()
  private[this] var repr: Array[Int] = null
  private[this] val lookup: Map[(Int, Int), (Int, Int, Int)] = Map()
  private[this] var useList: Array[ListBuffer[(Int, Int, Int)]] = null
  private[this] var classList: Array[ListBuffer[Int]] = null

  //for each constant, the parent constant in the proof node, or -1 if root
  private[this] var proofForest: Array[Int] = null
  private[this] var proofLabels: Array[MergePair] = null

  //initialize the state with the total number of constants
  //constants will then be identified by integer between 0 and 1
  def initialize(nbConstants: Int): Unit = {
    this.nbConstants = nbConstants
    repr = (0 until nbConstants).toArray
    classList = (0 until nbConstants).map(c => {
      val list = new ListBuffer[Int]
      list.append(c)
      list
    }).toArray
    useList = Array.fill(nbConstants)(new ListBuffer)
    proofForest = Array.fill(nbConstants)(-1)
    proofLabels = new Array(nbConstants)
  }

  def merge(eq: InputEquation): Unit = eq match {
    case Left((a, b)) => merge(a, b)
    case Right((a1, a2, a)) => merge(a1, a2, a)
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
        pendingMerges.enqueue(Right(((a1, a2, a), (b1, b2, b))))
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
      val e: MergePair = pendingMerges.dequeue()
      
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
        proofInsertEdge(a, b, e)
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

  private def proofReverseEdges(from: Int): Unit = {
    var previous = -1
    var previousLabel: MergePair = null
    var current = from
    while(current != -1) {
      val next = proofForest(current)
      val currentLabel = proofLabels(current)
      proofForest(current) = previous
      proofLabels(current) = previousLabel
      previous = current
      current = next
      previousLabel = currentLabel
    }
  }
  
  private def proofInsertEdge(from: Int, to: Int, e: MergePair) = {
    proofReverseEdges(from)
    proofForest(from) = to
    proofLabels(from) = e
  }

  // removes the edge from to from.parent and reverses the edges in order to
  // restore the state before the edge was inserted (mind the order of edge insertions)
  //private def removeEdge(from: Int, reversedTo: Int) {
  //  // not clearing edge label is fine as parent is null anyhow
  //  proofForest(from) = -1
  //  reverseEdges(reversedTo)
  //}
  
  //private def makeEdge(from: Int, to: Int, label: Pair[Formula, Formula]): Int =  {
  //  val retVal = reverseEdges(from)
  //  proofStructure(from) = to
  //  proofLabels(from) = label
  //  retVal
  //}
  
  //explain must return a subset of input equations (that were given through merge) that
  //explains why a = b. Requires that a=b
  def explain(a: Int, b: Int): Set[InputEquation] = {
    var acc: Set[InputEquation] = Set()
    def add(pair: MergePair) = if(pair != null) pair match {
      case Left((a, b)) => 
        acc += Left((a, b))
      case Right(((a1, a2, a), (b1, b2, b))) => {
        acc ++= explain(a1, b1)
        acc ++= explain(a2, b2)
        acc += Right((a1, a2, a))
        acc += Right((b1, b2, b))
      }
    }

    val seen: Array[Boolean] = Array.fill(nbConstants)(false)
    var ancestorA = a
    var ancestorB = b
    while(proofForest(ancestorA) != -1) {
      seen(ancestorA) = true
      ancestorA = proofForest(ancestorA)
    }
    while(proofForest(ancestorB) != -1 && !seen(ancestorB)) {
      ancestorB = proofForest(ancestorB)
    }

    require(ancestorB == ancestorA || proofForest(ancestorB) != -1)
    val commonAncestor = ancestorB
    ancestorA = a
    ancestorB = b
    while(ancestorA != commonAncestor) {
      add(proofLabels(ancestorA))
      ancestorA = proofForest(ancestorA)
    }
    while(ancestorB != commonAncestor) {
      add(proofLabels(ancestorB))
      ancestorB = proofForest(ancestorB)
    }
    acc
  }

  //// l is t-consequence of setTrue(lPrime)
  //def explain(l: Formula, lPrime: Formula = null): Set[Formula] = {
  //  val restoreIStack = Stack[Pair[Int, Formula]]()
  //  if(lPrime != null) {
  //    // undo all merges after lPrime was pushed onto the iStack
  //    var j = 0
  //    while(iStack(j)._2 != lPrime) {
  //      restoreIStack.push(iStack(j))

  //      j += 1
  //      if(j == iStack.size)
  //        throw new Exception("lPrime was not pushed to iStack")
  //    }
  //    backtrack(j)
  //  }

  //  // actual explain computation
  //  val retVal = l match{
  //    case Equals((e1: Variable), (d1: Variable)) => {
  //      explain(termToId(e1), termToId(d1))
  //    }
  //    case Not(Equals((d1: Variable), (e1: Variable))) => {
  //      // TODO can the causes for an inequality be stored better?
  //      val cause = diseq(repr(termToId(d1))).find{
  //        case (t,elem,_) => t.isValid && repr(elem) == repr(termToId(e1))
  //      }._3

  //      val Not(Equals((d2: Variable), (e2: Variable))) = cause

  //      // Checking for 1 congruence is enough. If d1 congruent e2 as well, that
  //      // would mean that d1 = d2 AND d1 = e2 AND d2 != e2, which is
  //      // inconsistent
  //      val d1Id = termToId(d1); val d2Id = termToId(d2)
  //      val e1Id = termToId(e1); val e2Id = termToId(e2)
  //      if(areCongruent(d1,d2)) {
  //        (explain(d1Id, d2Id) union explain(e1Id, e2Id)) + cause
  //      } else {
  //        (explain(d1Id, e2Id) union explain(e1Id, d2Id)) + cause
  //      }
  //    }
  //    case _ => throw new Exception("explain called on unsupported formula type "+ l)
  //  }


  //  if(lPrime != null) {
  //    // restore state after computing the explanation
  //    while(!restoreIStack.isEmpty) {
  //      val top = restoreIStack.pop
  //      ctr = top._1 - 1

  //      val validTimestamp = new Timestamp(iStack.size + 1, ctr + 1)
  //      invalidTimestamps -= validTimestamp

  //      setTrue(top._2)
  //    }
  //  }

  //  retVal
  //}

  //private def explain(c1: Int, c2: Int): Set[Formula] = {
  //  var id = -1
  //  var i = 0
  //  while(i < eqClass.size) {
  //    eqClass(i) = i
  //    i += 1
  //  }
  //  var explanation = new ListBuffer[Formula]
  //  pendingProofs.enqueue((c1, c2))

  //  while(pendingProofs.nonEmpty) {
  //    val (a, b) = pendingProofs.dequeue()
  //    val c = computeHighestNode(findEqClass(
  //      nearestCommonAncestor(a, b) match {
  //        case -1 => throw new Exception("No common ancestor "+ (idToTerm(a),idToTerm(b)))
  //        case x => x
  //      }
  //    ))
  //    explanation ++= explainAlongPath(a, c)
  //    explanation ++= explainAlongPath(b, c)
  //  }
  //  explanation.toSet
  //}

  //private def explainAlongPath(aL: Int, c: Int): ListBuffer[Formula] = {
  //  var explanation = new ListBuffer[Formula]
  //  var a = computeHighestNode(aL)
  //  while(a != c) {
  //    val b = proofStructure(a)
  //    proofLabels(a) match {
  //      case (eq@Equals(a: Variable, b: Variable), null) => explanation += eq
  //      case (Equals(fa@Apply(a1, a2), a: Variable),
  //            Equals(fb@Apply(b1, b2), b: Variable)) => {
  //        
  //        // commented out, because all the functions are added to the instance
  //        // for good anyhow, so no need to reuse them.
  //        //explanation += Equals(fa, a)
  //        //explanation += Equals(fb, b)

  //        pendingProofs.enqueue((termToId(a1), termToId(b1)))
  //        pendingProofs.enqueue((termToId(a2), termToId(b2)))
  //      }
  //      case _ => throw new Exception("Can't match edgeLabel "+ proofLabels(a))
  //    }
  //    // UNION
  //    eqClass(findEqClass(a)) = findEqClass(b)

  //    a = computeHighestNode(b)
  //  }
  //  explanation
  //}

}

object FastCongruenceClosure {
  sealed trait ApplyConstantTerms
  case class Constant(c: Int) extends ApplyConstantTerms
  case class Apply(t1: ApplyConstantTerms, t2: ApplyConstantTerms) extends ApplyConstantTerms
}
