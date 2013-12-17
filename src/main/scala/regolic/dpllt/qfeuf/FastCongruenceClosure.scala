package regolic
package dpllt
package qfeuf 

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import util.{HasLogger, Logger}

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer

trait FastCongruenceClosureComponent { this: AbstractComponent =>

  type Solver = FastCongruenceClosure
  def makeSolver(cnf: Set[Set[Literal]]): Solver = {
    val s = new FastCongruenceClosure
    s.initialize(cnf.flatten)

  /*
   * Algorithm described in "Fast congruence closure and extensions"
   * by Robert Nieuwenhuis and Albert Oliveras
   * Handle conjunctions of a = b or f(a,b) = c, where a,b and c are
   * constants. A conjunction of literals in the euf can always be rewriten
   * this way. The solver assume the constants are numbered from 0 to N, with N+1
   * different constatns.
   */
  class FastCongruenceClosure(implicit val context: Context) extends AbstractSolver {

    //TODO
    override def check = true

    private[this] implicit val tag = new Logger.Tag("Congruence Closure")

    import FastCongruenceClosure._

    private[this] val iStack = new Stack[Literal]

    private[this] var diseqs: Array[List[Int]] = null
    private[this] var posLits: Array[List[(Int, Int)]] = null
    private[this] var negLits: Array[List[(Int, Int)]] = null
    private[this] var diseqCauses: Map[(Int, Int), (Int, Int)] = new HashMap()

    private[this] var nbConstants = 0

    private[this] val pendingMerges: Queue[MergePair] = Queue()
    private[this] var repr: Array[Int] = null
    private[this] var lookup: Map[(Int, Int), (Int, Int, Int)] = new HashMap()
    private[this] var useList: Array[ListBuffer[(Int, Int, Int)]] = null
    private[this] var classList: Array[ListBuffer[Int]] = null

    //for each constant, the parent constant in the proof node, or -1 if root
    private[this] var proofForest: Array[Int] = null
    //the label is for the edge outgoing from the corresponding node
    private[this] var proofLabels: Array[MergePair] = null

    //stacks of changes to the data structures, sync with iStack
    private[this] val undoReprChangesStack = new Stack[Stack[(Int, Int, Int)]]
    private[this] val undoDiseqsStack = new Stack[Array[List[Int]]]
    private[this] val undoLookupStack = new Stack[Map[(Int, Int), (Int, Int, Int)]]
    private[this] val undoUseListStack = new Stack[Array[ListBuffer[(Int, Int, Int)]]]
    private[this] val undoEdgesStack = new Stack[Stack[(Int, Int)]]

    private[this] val literalsId = new HashMap[(Int, Int), Int]

    def initialize(lits: Set[dpllt.Literal]): Unit = {
      val nbConstants = lits.map{ 
        case Literal(Left((a,b)), _, _, _) => a.max(b)
        case Literal(Right((a,b,c)), _, _, _) => a.max(b).max(c)
        case _ => 0
      }.max + 1
      initialize(nbConstants, lits) 
    }
    /*
     * initialize with nbConstants N (then constant are identified from 0 to N-1)
     *
     * The lits set is optional and should be used as an optimization for the solver.
     * For example, theory consequences after a merge will be drawned from those literals.
     * But if the set is empty, it will not affect completeness or soundness.
     *
     * TODO: should the theory propagation be complete for the given lits set ?
     */
    def initialize(nbConstants: Int, lits: Set[dpllt.Literal] = Set()): Unit = {
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
      posLits = Array.fill(nbConstants)(List())
      negLits = Array.fill(nbConstants)(List())
      diseqs = Array.fill(nbConstants)(List())
      lits.map(lit => lit match {
        case Literal(Left(eq@(a, b)), id, pol, _) => {
          literalsId((a, b)) = id
          if(pol) {
            posLits(a) ::= eq
            posLits(b) ::= eq
          } else {
            negLits(a) ::= eq
            negLits(b) ::= eq
          }
        }
        case _ => ()
      })
      undoReprChangesStack.push(new Stack()) //TODO: this is a hack to support stacking change from merge without setTrue
      //undoUseListStack.push(new Stack()) //TODO: this is a hack to support stacking change from merge without setTrue
      undoEdgesStack.push(new Stack()) //TODO: this is a hack to support stacking change from merge without setTrue
      invariant()
    }

    def setTrue(lit: dpllt.Literal): Set[dpllt.Literal] = {
      val l@Literal(ie, id, pol, _) = lit
      ie match {
        case Left((a, b)) => literalsId((a, b)) = id
        case _ => assert(false)
      }
      iStack.push(l)
      undoReprChangesStack.push(new Stack)
      undoEdgesStack.push(new Stack)
      undoDiseqsStack.push(diseqs.clone)
      undoLookupStack.push(lookup.clone)
      undoUseListStack.push(useList.map(buf => buf.clone))
      val res = if(pol) {
        merge(ie).filterNot(l => l.id == lit.id && l.polInt == lit.polInt)
      } else {
        //assuming disequalities are only between constants, due to flattener
        val Left((a, b)) = ie
        if(areCongruent(a, b))
          throw new InconsistencyException
        val aRep = repr(a)
        val bRep = repr(b)

        // Computing the T-consequences
        val (cla, clb) = (classList(aRep), classList(bRep))
        val cl = if(cla.size < clb.size) cla else clb
        val tConsequences = ListBuffer[dpllt.Literal]()
        for(c <- cl) {
          for((c1, c2) <- negLits(c)) {
            if(!diseqs(repr(c1)).contains(repr(c2))) {
              if((repr(c1) == aRep && repr(c2) == bRep) ||
                 (repr(c1) == bRep && repr(c2) == aRep)) {
                diseqCauses((c1, c2)) = ((a, b))
                tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), false, null)
              }
            }
          }
        }

        diseqs(aRep) ::= bRep
        diseqs(bRep) ::= aRep

        tConsequences.toSet.filterNot(l => l.id == lit.id && l.polInt == lit.polInt)
      }
      invariant()
      res
    }


    def merge(eq: InputEquation): Set[dpllt.Literal] = eq match {
      case Left((a, b)) => merge(a, b)
      case Right((a1, a2, a)) => merge(a1, a2, a)
    }

    def merge(a: Int, b: Int): Set[dpllt.Literal] = {
      pendingMerges.enqueue(Left((a, b)))
      propagate()
    }
    def merge(a1: Int, a2: Int, a: Int): Set[dpllt.Literal] = {
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
          Set() // no new unions, no T-consequences
        }
      }
    }

    //returns original input diseq that made those representatives different
    private def wthAreThoseDifferent(aRep: Int, bRep: Int): (Int, Int) = {
      iStack.flatMap{
        case Literal(Left((c1, c2)), _, false, _) => 
          if((repr(c1) == aRep && repr(c2) == bRep) || (repr(c1) == bRep && repr(c2) == aRep))
            List((c1, c2))
          else
            List()
        case _ => List()
      }.head //optimistically get the head of a list, should be fine, don't worry
    }

    //return set of consequences
    private def propagate(): Set[dpllt.Literal] = {
      val tConsequences = ListBuffer[Literal]()
      while(pendingMerges.nonEmpty) {
        val e: MergePair = pendingMerges.dequeue()
        
        val (a, b) = {
          val (aTmp, bTmp) = e match {
            case Left((a, b)) => (a, b)
            case Right(((_, _, a), (_, _, b))) => (a, b)
          }
          if(classList(repr(aTmp)).size > classList(repr(bTmp)).size)
            (bTmp, aTmp)
          else 
            (aTmp, bTmp)
        }

        val aRep = repr(a)
        val bRep = repr(b)

        if(aRep != bRep) { //aRep will be replaced by bRep
          if(diseqs(aRep).exists(c => c == bRep)) {
            pendingMerges.clear()
            throw new InconsistencyException
          }

          for(c <- classList(aRep)) {
            for((c1, c2) <- posLits(c)) {
              if((repr(c1) == aRep && repr(c2) == bRep) || //TODO: posLits(x) should have (x, y), x always on the left
                 (repr(c1) == bRep && repr(c2) == aRep))
                tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), true, null)
            }
            for((c1, c2) <- negLits(c)) {
              if(repr(c1) == aRep) {
                if(!diseqs(aRep).contains(repr(c2)) && diseqs(bRep).contains(repr(c2))) {
                  //TODO: (same for the other diseqCauses) the order of (a, b) may not correspond to the literal order and may fail to return the exact same literal (commutativity)
                  diseqCauses((c1, c2)) = wthAreThoseDifferent(bRep, repr(c2))
                  tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), false, null)
                }
              } else if(repr(c2) == aRep) {
                if(!diseqs(aRep).contains(repr(c1)) && diseqs(bRep).contains(repr(c1))) {
                  diseqCauses((c1, c2)) = wthAreThoseDifferent(bRep, repr(c1))
                  tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), false, null)
                }
              }
            }
          }
          for(c <- classList(bRep)) {
            for((c1, c2) <- negLits(c)) {
              if(repr(c1) == bRep) {
                if(!diseqs(bRep).contains(repr(c2)) && diseqs(aRep).contains(repr(c2))) {
                  diseqCauses((c1, c2)) = wthAreThoseDifferent(aRep, repr(c2))
                  tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), false, null)
                }
              } else if(repr(c2) == bRep) {
                if(!diseqs(bRep).contains(repr(c1)) &&diseqs(aRep).contains(repr(c1))) {
                  diseqCauses((c1, c2)) = wthAreThoseDifferent(aRep, repr(c1))
                  tConsequences += Literal(Left((c1, c2)), literalsId((c1, c2)), false, null)
                }
              }
            }
          }

          diseqs(aRep).foreach(c => {
            diseqs(bRep) ::= c
            //should remove aRep from the diseqs list of c as well and replaced by bRep
            //aRep is only present in the diseqs list of the elements in its own list
            diseqs(c) = diseqs(c).map(d => if(d == aRep) bRep else d)
          })
          diseqs(aRep) = Nil

          proofInsertEdge(a, b, e)
          classList(aRep).foreach(c => {
            undoReprChangesStack.top.push((c, aRep, bRep))
            repr(c) = bRep
            classList(bRep).append(c)
          })
          classList(aRep).clear()

          useList(aRep).foreach{case f1@(c1, c2, c) => {
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
          useList(aRep).clear()
        }
      }
      tConsequences.toSet
    }
    
    def areCongruent(ie: InputEquation): Boolean = ie match {
      case Left((a, b)) => areCongruent(a, b)
      case Right((a,b,c)) => areCongruent(Apply(Constant(a), Constant(b)), Constant(c))
    }
    def areCongruent(a: Int, b: Int): Boolean = areCongruent(Constant(a), Constant(b))
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

    //reverse all edges on the path from <from> to the root, and return the root
    private def proofReverseEdges(from: Int): Int = {
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
      previous
    }
    
    private def proofInsertEdge(from: Int, to: Int, e: MergePair): Unit = {
      val previousRoot = proofReverseEdges(from)
      proofForest(from) = to
      proofLabels(from) = e

      undoEdgesStack.top.push((from, previousRoot))
    }

    // removes the edge from to from.parent and reverses the edges in order to
    // restore the state before the edge was inserted (mind the order of edge insertions)
    private def proofRemoveEdge(from: Int, reversedTo: Int): Unit = {
      //not clearing edge label is fine as parent is null anyhow
      proofForest(from) = -1
      proofReverseEdges(reversedTo)
    }
    
    //private def makeEdge(from: Int, to: Int, label: Pair[Formula, Formula]): Int =  {
    //  val retVal = reverseEdges(from)
    //  proofStructure(from) = to
    //  proofLabels(from) = label
    //  retVal
    //}
    
    /*
     * explain must return a subset of input equations (that were given through merge) that
     * explains why a = b. Requires that a=b
     *
     * There can be, in general, many different explanations. We do not guarantee any
     * particular explanation, other than the fact that the explanation consists of a
     * subset of the input equations passed through merge operations.
     */
    def explain(a: Int, b: Int): Set[InputEquation] = {
      require(areCongruent(a, b))
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

    def explanation(l: dpllt.Literal): Set[dpllt.Literal] = {
      //TODO: is it necessary to backtrack to l' (such that setTrue(l') propagates l)
      //      and then restore ?
      val Literal(eq, _, pol, _) = l
      val res: Set[dpllt.Literal] = if(pol) {
        val Left((a, b)) = eq
        explain(a, b).flatMap{
          case Left((a, b)) => List(Literal(Left((a,b)), literalsId((a, b)), true, null))
          case Right((a, b, c)) => List()//Literal(Right((a,b,c)), 0, true, null)
        }
      } else {
        val Left((d1, e1)) = eq
        val (d2, e2) = diseqCauses((d1, e1)) //d2 != e2 is the cause of d1 != e1

        // Checking for 1 congruence is enough. If d1 congruent e2 as well, that
        // would mean that d1 = d2 AND d1 = e2 AND d2 != e2, which is
        // inconsistent
        val rec = if(areCongruent(d1, d2)) {
          (explain(d1, d2) union explain(e1, e2))
        } else {
          (explain(d1, e2) union explain(e1, d2))
        }

        //rec.map(i => Literal(i, 0, true, null): dpllt.Literal) + 
        rec.flatMap{
          case Left((a, b)) => List(Literal(Left((a,b)), literalsId((a, b)), true, null))
          case Right((a, b, c)) => List()//Literal(Right((a,b,c)), 0, true, null)
        }.toSet + Literal(Left(d2, e2), literalsId((d2, e2)), false, null)
      }
      logger.debug("Theory explanation for literal [" + l + "] is " + res.mkString("[", ", ", "]"))
      assert(res.forall(lit => isTrue(lit)))
      res
    }

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


    def isTrue(lit: dpllt.Literal): Boolean = {
      val Literal(ie, _, pol, _) = lit
      if(pol) {
        areCongruent(ie)
      } else {
        val Left((a, b)) = ie
        val repA = repr(a)
        val repB = repr(b)
        diseqs(repA).indexOf(repB) != -1 ||
        diseqs(repB).indexOf(repA) != -1
      }
    }

    def backtrack(n: Int): Unit = backtrack(n, null)
    def backtrack(n: Int, lit: dpllt.Literal): Unit = {
      if(n > iStack.size)
        throw new Exception("Can't pop "+ n +" literals from I-stack.")
      else {
        1 to n foreach { _ => {
          val poppedLit = iStack.pop
          logger.debug("backtracking literal " + poppedLit)
          if(lit != null) {
            logger.trace("expected to backtrack literal " + lit)
            assert(lit.id == poppedLit.id && lit.polInt == poppedLit.polInt)
          }

          val reprChanges = undoReprChangesStack.pop
          while(!reprChanges.isEmpty) {
            val (elem, oldRepr, newRepr) = reprChanges.pop
            repr(elem) = oldRepr
            classList(newRepr) -= elem
            classList(oldRepr).append(elem)
          }

          val edgeChanges = undoEdgesStack.pop
          while(!edgeChanges.isEmpty) {
            val (from, reversedTo) = edgeChanges.pop
            proofRemoveEdge(from, reversedTo)
          }


          //val useListChanges = undoUseListStack.pop
          //while(!useListChanges.isEmpty) {
          //  val (f, oldRepr, newRepr) = undoUseListStack(l).pop
          //  useList(oldRepr).prepend(f)
          //  if(newRepr != -1) {
          //    val index = useList(newRepr).indexWhere(_ == f)
          //    useList(newRepr).remove(index)
          //  }
          //}
          useList = undoUseListStack.pop
    
          diseqs = undoDiseqsStack.pop
          lookup = undoLookupStack.pop
        }}
      }
      invariant()
    }

    def undoInvariant(): Unit = {
      assert(undoReprChangesStack.size == iStack.size + 1)
      assert(undoDiseqsStack.size == iStack.size)
      assert(undoUseListStack.size == iStack.size)
    }

    def useListInvariant(): Unit = {
      useList.zipWithIndex.foreach{ case (list, a) => {
        if(!list.isEmpty)
          assert(repr(a) == a)
        list.foreach{case (c1, c2, c) => {
          assert(repr(c1) == a || repr(c2) == a)
        }}
      }}
    }

    def classListInvariant(): Unit = {
      val seen = Array.fill(nbConstants)(false)
      classList.zipWithIndex.foreach{ case (list, a) => {
        if(!list.isEmpty)
          assert(repr(a) == a)
        list.foreach(b => {
          assert(!seen(b))
          seen(b) = true
        })
      }}
      assert(seen.forall(b => b))
    }

    //diseqs only store disequalities between representative
    def diseqsInvariant(): Unit = {
      diseqs.zipWithIndex.foreach{ case (list, a) => {
        if(!list.isEmpty) {
          assert(repr(a) == a)
          assert(list.forall(b => repr(b) == b))
        }
      }}
    }

    def invariant(): Unit = {
      classListInvariant()
      useListInvariant()
      diseqsInvariant()
      undoInvariant()
      assert(pendingMerges.isEmpty)
    }

  }

  object FastCongruenceClosure {

    sealed trait ApplyConstantTerms
    case class Constant(c: Int) extends ApplyConstantTerms
    case class Apply(t1: ApplyConstantTerms, t2: ApplyConstantTerms) extends ApplyConstantTerms

    type InputEquation = Either[(Int, Int), (Int, Int, Int)]
    type MergePair = Either[
                       Tuple2[Int, Int],
                       Tuple2[(Int, Int, Int), (Int, Int, Int)]
                     ]

  }

  //class PreProcessing {
  //
  //  def apply(cnf: Set[Set[Formula]]): Set[Set[smt.Literal]] = {
  //
  //    var namesToConstants: Map[String, Int] = {
  //      var constantId = -1
  //      new HashMap[String, Int] {
  //        override def apply(name: String): Int = this.get(name) match {
  //          case Some(id) => id
  //          case None => {
  //            constantId += 1
  //            this(name) = constantId
  //            constantId
  //          }
  //        }
  //      }
  //    }
  //
  //    var extraDefs: List[FastCongruenceClosure.InputEquation] = List()
  //
  //    def addName(p: (String, FunctionApplication)): Unit = p match {
  //      case (a, Apply(FunctionApplication(FunctionSymbol(a1, _, _), _), FunctionApplication(FunctionSymbol(a2, _, _), _))) =>
  //        extraDefs ::= Right((namesToConstants(a1), namesToConstants(a2), namesToConstants(a)))
  //      case (a, FunctionApplication(FunctionSymbol(b, _, _), _)) =>
  //        extraDefs ::= Left((namesToConstants(a), namesToConstants(b)))
  //    }
  //
  //    val processed: List[List[smt.Literal]] = cnf.toList.map(clause => clause.toList.map(lit => lit match {
  //      case eq@Equals(t1, t2) => {
  //        val ct1 = Currifier(t1)
  //        val ct2 = Currifier(t2)
  //        val (Variable(name1, _), names1) = Flattener.transform(ct1)
  //        val (Variable(name2, _), names2) = Flattener.transform(ct2)
  //        names1.foreach(p => addName(p))
  //        names2.foreach(p => addName(p))
  //        Literal(
  //          Left((namesToConstants(name1), namesToConstants(name2))),
  //          0,
  //          true,
  //          eq
  //        )
  //
  //      }
  //      case Not(eq@Equals(t1, t2)) => {
  //        val ct1 = Currifier(t1)
  //        val ct2 = Currifier(t2)
  //        val (Variable(name1, _), names1) = Flattener.transform(ct1)
  //        val (Variable(name2, _), names2) = Flattener.transform(ct2)
  //        names1.foreach(p => addName(p))
  //        names2.foreach(p => addName(p))
  //        Literal(
  //          Left((namesToConstants(name1), namesToConstants(name2))),
  //          0,
  //          false,
  //          eq
  //        )
  //      }
  //    }))
  //
  //    processed.map(clause => clause.toSet).toSet ++ extraDefs.map(ie => Set[smt.Literal](Literal(ie, 0, true, null))).toSet
  //
  //  }
  //
  //}

}
