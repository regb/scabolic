package regolic.smt.qfeuf 

import regolic.smt.Solver
import regolic.smt.TheorySolver
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.Trees.IntSort

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer

import regolic.StopWatch

//object FastCongruenceSolver extends Solver {
  //val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  //def isSat(f: Formula): Pair[Boolean, Option[collection.immutable.Map[Formula, Set[Formula]]]] = {
    //val And(fs) = f

    //val neqs = Map[Formula, Formula]()
    //val transformedToEq: collection.immutable.Map[Formula, Formula] = fs.flatMap{
      //case eq@Equals(_, _) => Flattener(Currifier(eq)).map(l => (l, eq))
      //case Not(eq@Equals(_, _)) => {
        //val eqs = Flattener(Currifier(eq))
        //neqs(eqs.head) = eq
        //eqs.tail.map(l => (l, eq))
      //}
      //case _ => None
    //}.toMap
      
    //val transformedEqs = transformedToEq.keySet
    //val congruenceClosure = new CongruenceClosure
    //congruenceClosure.initialize(transformedEqs)
    //transformedEqs.foreach(congruenceClosure.merge)

    //val unsatTerms = neqs.keys.filter{
      //// Are two variables, which shouldn't be equal congruent?
      //case Equals(t1, t2) if congruenceClosure.areCongruent(t1, t2) => true
      //case _ => false
    //}.toList

    //// For each such inequality, get the explanation why it must be an equality
    //val explanations: collection.immutable.Map[Formula, Set[Formula]] = unsatTerms.map{
      //case eq@Equals((t1: Variable), (t2: Variable)) => (neqs(eq),
        //congruenceClosure.explain(t1, t2).withFilter{
            /*
             * Only use equalities between variables
             */
            //case Equals((v1: Variable), (v2: Variable)) => true
            //case _ => false
          //}.map(transformedToEq(_)))
    //}.toMap

    //if(unsatTerms.isEmpty)
      //(true, None) // TODO what consequences to return for T-propagation?
    //else
      //(false, Some(explanations))
  //}

//}

/*
 * Algorithm as described in "Fast congruence closure and extensions" by
 * Nieuwenhuis and Oliveras
 */
class CongruenceClosure extends TheorySolver {

  val logic = regolic.parsers.SmtLib2.Trees.QF_UF
  
  var time: Double = 0.0f
  var reason: Formula = null
    
  private var posLitList: Array[Array[Formula]] = null
  private var negLitList: Array[Array[Formula]] = null

  private val termToId = Map[Term, Int]()
  private var idToTerm: Array[Term] = null

  private var repr: Array[Int] = null
  private val lookup: Map[(Int, Int), Pair[Timestamp, Formula]] = Map()
  // We need to be able to both append and prepend (when backtracking), which a
  // queue does not support 
  private var useList: Array[ListBuffer[Formula]] = null
  private var classList: Array[ArrayBuffer[Int]] = null

  private val pendingMerges: Queue[Pair[Formula, Formula]] = Queue()

  private val iStack = new Stack[Pair[Int, Formula]]
  // Maybe try representing diseq with a map or a 2-dimensional array
  private var diseq: Array[ListBuffer[Tuple3[Timestamp,Int,Formula]]] = null

  //var negReason = Map[Formula, Formula]()

  private var trigger: Formula = null

  private val undoReprChangeStack = new HashMap[Formula, Stack[Pair[Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[Int, Int]]()
      this += (k -> v)
      v
    }
  }
  private val undoUseListStack = new HashMap[Formula, Stack[Tuple3[Formula, Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Tuple3[Formula, Int, Int]]()
      this += (k -> v)
      v
    }
  }
  private val undoEdgesStack = new HashMap[Formula, Stack[Pair[Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[Int, Int]]()
      this += (k -> v)
      v
    }
  }

  class Timestamp(private val height: Int, private val ctr: Int) {
    // check for containment should be O(1)
    def isValid = !invalidTimestamps.contains(this)
    override def toString: String = "[height: "+ height +", ctr: "+ ctr +"]"

    override def equals(other: Any): Boolean = other match{
      case that: Timestamp =>
        (that canEqual this) &&
        this.height == that.height &&
        this.ctr == that.ctr
      case _ => false
    }

    def canEqual(other: Any) = other.isInstanceOf[Timestamp]

    override def hashCode: Int = 41 * ( 41 + height) + ctr
  }
  private val invalidTimestamps = collection.mutable.Set[Timestamp]()
  private var currentTimestamp: Timestamp = null
  private var ctr: Int = 0

  private val pendingProofs: Queue[Pair[Int,Int]] = Queue()
  private var eqClass: Array[Int] = null
  private var proofStructure: Array[Int] = null
  private var proofLabels: Array[Pair[Formula, Formula]] = null
  
  private[this] val sw = StopWatch("ccStopwatch")
  
  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
    

  def initialize(ls: Set[Formula]) {//I.e. constructor
    val terms = collection.mutable.Set[Term]()

    val pos = new HashMap[Term, collection.mutable.Set[Formula]] {
      override def default(k: Term) = {
        val v = collection.mutable.Set[Formula]()
        this += (k -> v)
        v
      }
    }
    val neg = new HashMap[Term, collection.mutable.Set[Formula]] {
      override def default(k: Term) = {
        val v = collection.mutable.Set[Formula]()
        this += (k -> v)
        v
      }
    }
    
    for(l <- ls) {
      l match {
        case Equals(t1, t2) => {
          terms ++= extractVariables(t1)
          terms ++= extractVariables(t2)
          if(t1.isInstanceOf[Variable] && t2.isInstanceOf[Variable]) {
            pos(t1) += l
            pos(t2) += l
          }
        }
        case Not(eq@Equals((t1: Variable), (t2: Variable))) => {
          // TODO we should check if the repr exists when we setTrue an
          // inequality and return an Error if not, rather than adding them for
          // all variables
          //terms ++= extractVariables(t1)
          //terms ++= extractVariables(t2)
          neg(t1) += l
          neg(t2) += l
        }
        case _ => throw new Exception("Unsupported formula type: "+ l)
      }
    }

    val numTerms = terms.size
    repr = new Array(numTerms)
    classList = new Array(numTerms)
    useList = new Array(numTerms)
    diseq = new Array(numTerms)
    proofStructure = new Array(numTerms)
    proofLabels = new Array(numTerms)
    posLitList = new Array(numTerms)
    negLitList = new Array(numTerms)

    eqClass = new Array(numTerms)

    idToTerm = new Array(numTerms)

    var id = -1
    for(t <- terms) {
      id += 1

      termToId += (t -> id)
      idToTerm(id) = t

      posLitList(id) = pos(t).toArray
      negLitList(id) = neg(t).toArray

      repr(id) = id
      classList(id) = ArrayBuffer()
      classList(id) += id
      useList(id) = ListBuffer()
      diseq(id) = ListBuffer()

      proofStructure(id) = -1
      eqClass(id) = id
    }
  }

  // Every call to setTrue needs to push a literal to the iStack, so that
  // backtracking is possible for each T-literal enqueued in the DPLL engine
  def setTrue(l: Formula): Option[Set[Formula]] = {
    trigger = l
    ctr += 1
    iStack.push((ctr, l))
    reason = null
    currentTimestamp = new Timestamp(iStack.size, ctr)

    val retVal = l match {
      case Equals(_,_) => {
        //merge(eq)
        val tmp = merge(l)
        tmp match {
          case None => None
          case _ => Some(Set.empty[Formula])
        }
      }
      case Not(Equals(t1,t2)) => {
        if(!areCongruent(t1, t2)) {
          //Diseq, a hash table containing all currently true disequalities between
          //representatives
          val t1Id = termToId(t1); val t2Id = termToId(t2)
          diseq(repr(t1Id)) += Tuple3(currentTimestamp, repr(t2Id), trigger)
          diseq(repr(t2Id)) += Tuple3(currentTimestamp, repr(t1Id), trigger)

          // Computing the T-consequences
          val (a, b) = (repr(t1Id), repr(t2Id))
          val (cla, clb) = (classList(a), classList(b))
          val cl = if(cla.size < clb.size) cla else clb
          val tConsequence = ListBuffer[Formula]()
          for(c <- cl) {
            tConsequence ++= negLitList(c).filter{
              case Not(Equals(s1, s2)) => {
                val s1Id = termToId(s1); val s2Id = termToId(s2)
                (repr(s1Id) == a && repr(s2Id) == b) ||
                (repr(s1Id) == b && repr(s2Id) == a) 
              }
            }
          }

          //negReason ++= tConsequence.map(ineq => (ineq, l))
          //println("negReason: "+ negReason.mkString("\n", "\n", "\n"))
          //Some(tConsequence.toSet)
          Some(Set.empty[Formula])
        } else {
          reason = Equals(t1, t2)
          None // inconsistent
        }
      }
    }
    retVal
  }

  private def merge(eq: Formula): Option[Set[Formula]] = {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pendingMerges.enqueue((eq, null))
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        val a1Id = termToId(a1); val a2Id = termToId(a2)
        val lookedUp = lookup.getOrElse((repr(a1Id), repr(a2Id)), null)
        if(lookedUp != null && lookedUp._1.isValid) {
          pendingMerges.enqueue((eq, lookedUp._2))
          propagate()
        } else {
          lookup += ((repr(a1Id), repr(a2Id)) -> (currentTimestamp, eq))
          useList(repr(a1Id)).append(eq)
          useList(repr(a2Id)).append(eq)
          Some(Set.empty[Formula]) // no new unions, no T-consequences
        }
      }
    }
  }

  private def propagate(): Option[Set[Formula]] = {
    val tConsequence = ListBuffer[Formula]()
    while(pendingMerges.nonEmpty) {
      val e = pendingMerges.dequeue()
      
      val p = e match {
        case (Equals(a: Variable, b: Variable), null) => (termToId(a), termToId(b))
        case (Equals(_, a: Variable), Equals(_, b: Variable)) => (termToId(a), termToId(b))
      }
      val (a, b) = if(classList(repr(p._1)).size > classList(repr(p._2)).size){
        p.swap
      } else p

      // merge classes of a and b (a => b)
      if(repr(a) != repr(b)) {

        // trying to merge classes, which are disequal
        if(diseq(repr(a)).exists{case(t,v,_) => {t.isValid && repr(v) == repr(b)}}) {
          // If for some reason, the trigger literal causing this inconsistency
          // is not pushed onto the I-stack, make sure to set the timestamp
          // invalid here.
          // As it stands now, it gets taken care of in backtrack.
          reason = Not(Equals(idToTerm(a), idToTerm(b)))
          return None
        }

        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        for(c <- classList(oldreprA)) {
          tConsequence ++= posLitList(c).filter{
            case Equals(t1, t2) => {
              val t1Id = termToId(t1); val t2Id = termToId(t2)
              (repr(t1Id) == oldreprA && repr(t2Id) == repr(b)) || (repr(t1Id) == repr(b) && repr(t2Id) == oldreprA)
            }
          }

          assert(repr(c) == oldreprA)
          undoReprChangeStack(trigger).push((c, oldreprA))
          repr(c) = repr(b)
          classList(repr(b)).append(c)
        }
        classList(oldreprA).clear()

        for(d <- diseq(oldreprA)) {
          d match {
            case (t,v,reason1) if t.isValid => {
              diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)
            }
            // Removing while iterating possible with ListBuffer
            case _ => diseq(oldreprA) -= d
          }
        }

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
            undoUseListStack(trigger).push(Tuple3(f1, oldreprA, -1))
            pendingMerges.enqueue((f1, lookedUp._2))
          } else {
            lookup += ((repr(c1Id), repr(c2Id)) -> (currentTimestamp, f1))

            undoUseListStack(trigger).push(Tuple3(f1, oldreprA, repr(b)))
            useList(repr(b)).append(f1)
          }
        }
        useList(oldreprA).clear()
      } // if
    } // while
    Some(tConsequence.toSet)
  }
  
  def isTrue(l: Formula) = {
    l match {
      case Equals(t1, t2) => {
        areCongruent(t1, t2)
      }
      case Not(Equals(t1, t2)) => {
        !areCongruent(t1, t2)
      }
    }
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

  private def undoMerge(l: Formula) {
   /*
    * Example: 
    *   a -> b -> c -> d
    *   insert b -> e:
    *     a -> b <- c <- d
    *          '-> e
    *     from = b
    *     reversedTo = d
    *   undo b -> e:
    *     a -> b -> c -> d
    */
    while(!undoEdgesStack(l).isEmpty) {
      val (from, reversedTo) = undoEdgesStack(l).pop
      removeEdge(from, reversedTo)
    }

    while(!undoReprChangeStack(l).isEmpty) {
      val (elem, oldRepr) = undoReprChangeStack(l).pop
      val newRepr = repr(elem)
      repr(elem) = oldRepr
      classList(newRepr) -= elem
      classList(oldRepr).append(elem)
    }
    
    while(!undoUseListStack(l).isEmpty) {
      val (f, oldRepr, newRepr) = undoUseListStack(l).pop
      useList(oldRepr).prepend(f)
      if(newRepr != -1) {
        val index = useList(newRepr).indexWhere(_ == f)
        useList(newRepr).remove(index)
      }
    }
  
  }
  
  def backtrack(n: Int) {
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        val (topCtr, topTrigger) = iStack.pop
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        invalidTimestamps += delTimestamp

        undoMerge(topTrigger)
      }}

      pendingMerges.clear()

    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
  }

  def backtrackTo(l: Formula) {
    if(l != null) {
      var poppedLiteral: Formula = null
      do {
        val (topCtr, topTrigger) = iStack.pop
        poppedLiteral = topTrigger
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        invalidTimestamps += delTimestamp

        undoMerge(topTrigger)
      } while(poppedLiteral != l) 

      pendingMerges.clear()
    }
  }
  
  private def reverseEdges(from: Int) = {
    var p = from
    var q = -1
    var r = -1
    //var q: ProofStructureNode = null
    //var r: ProofStructureNode = null
    var qEdge: Pair[Formula, Formula] = null
    var rEdge: Pair[Formula, Formula] = null

    while(p != -1) {
      r = q
      q = p
      p = proofStructure(q)

      rEdge = qEdge
      qEdge = proofLabels(q)

      proofStructure(q) = r
      proofLabels(q) = rEdge
    }
    proofStructure(from) = -1
    q
  }

  // removes the edge from to from.parent and reverses the edges in order to
  // restore the state before the edge was inserted (mind the order of edge insertions)
  private def removeEdge(from: Int, reversedTo: Int) {
    // not clearing edge label is fine as parent is null anyhow
    proofStructure(from) = -1
    reverseEdges(reversedTo)
  }
  
  private def makeEdge(from: Int, to: Int, label: Pair[Formula, Formula]): Int =  {
    val retVal = reverseEdges(from)
    proofStructure(from) = to
    proofLabels(from) = label
    retVal
  }
  
  private def insertEdge(a: Int, b: Int, label: Pair[Formula, Formula]) = {
    val from = a
    val reversedTo = makeEdge(a, b, label)

    //println(node.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    undoEdgesStack(trigger).push((from, reversedTo))
  }
  
  private def findEqClass(x: Int): Int = {
    if(eqClass(x) == x)
      x
    else
      findEqClass(eqClass(x))
  }

  private def computeHighestNode(c: Int): Int = {
    @annotation.tailrec
    def nestedComputeHighestNode(x: Int): Int = {
      if(proofStructure(x) == -1 || findEqClass(proofStructure(x)) != findEqClass(c)) 
        x
      else
        nestedComputeHighestNode(proofStructure(x))
    }
    nestedComputeHighestNode(c)
  }

  private def nearestCommonAncestor(a: Int, b: Int): Int = {
    @annotation.tailrec
    def pathToRoot(n: Int, acc: List[Int] =
      Nil): List[Int] = {
      //println("n: "+ n.name +", "+ acc.length)
      if(proofStructure(n) != -1)
        pathToRoot(proofStructure(n), n :: acc)
      else
        n :: acc // Include root
    }

    // TODO some overhead due to functional implemenation
    val commonPath = pathToRoot(a).zip(pathToRoot(b)).filter{
      case (first, second) => first == second
    }
    if(commonPath.isEmpty)
      -1
    else
      commonPath.reverse.head._1
  }

  // l is t-consequence of setTrue(lPrime)
  def explain(l: Formula, lPrime: Formula = null): Set[Formula] = {
    val restoreIStack = Stack[Pair[Int, Formula]]()
    if(lPrime != null) {
      // undo all merges after lPrime was pushed onto the iStack
      var j = 0
      while(iStack(j)._2 != lPrime) {
        restoreIStack.push(iStack(j))

        j += 1
        if(j == iStack.size)
          throw new Exception("lPrime was not pushed to iStack")
      }
      backtrack(j)
    }

    // actual explain computation
    val retVal = l match{
      case Equals((e1: Variable), (d1: Variable)) => {
        explain(termToId(e1), termToId(d1))
      }
      case Not(Equals((d1: Variable), (e1: Variable))) => {
        //println("negReason: "+ negReason.mkString("\n", "\n", "\n"))
        //val cause = negReason(l)
        // if valid
        // TODO
        val cause = diseq(repr(termToId(d1))).find{case (t,elem,_) => t.isValid && repr(elem) == repr(termToId(e1))}.get._3

        val Not(Equals((d2: Variable), (e2: Variable))) = cause
        // Checking for 1 congruence is enough. If d1 congruent e2 as well, that
        // would mean that d1 = d2 AND d1 = e2 AND d2 != e2, which is
        // inconsistent
        val d1Id = termToId(d1); val d2Id = termToId(d2)
        val e1Id = termToId(e1); val e2Id = termToId(e2)
        //println(node.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
        if(areCongruent(d1,d2)) {
          (explain(d1Id, d2Id) union explain(e1Id, e2Id)) + cause
        } else {
          (explain(d1Id, e2Id) union explain(e1Id, d2Id)) + cause
        }
      }
      case _ => throw new Exception("explain called on unsupported formula type "+ l)
    }


    if(lPrime != null) {
      // restore state after computing the explanation
      while(!restoreIStack.isEmpty) {
        val top = restoreIStack.pop
        ctr = top._1 - 1

        val validTimestamp = new Timestamp(iStack.size + 1, ctr + 1)
        //println("making timestamp "+ validTimestamp +" valid again")
        invalidTimestamps -= validTimestamp

        setTrue(top._2)
      }
    }

    //println("explanation: "+ retVal.mkString("\n", "\n", "\n"))

    retVal
  }

  private def explain(c1: Int, c2: Int): Set[Formula] = {
    var id = -1
    for(i <- (0 until eqClass.size)) {
      eqClass(i) = i
    }
      sw.time {
      }
      time += sw.seconds
      sw.reset
    
    var explanation = new ListBuffer[Formula]
    pendingProofs.enqueue((c1, c2))

    while(pendingProofs.nonEmpty) {
      val (a, b) = pendingProofs.dequeue()
      val c = computeHighestNode(findEqClass(
        nearestCommonAncestor(a, b) match {
          case -1 => throw new Exception("No common ancestor "+ (idToTerm(a),idToTerm(b)))
          case x => x
        }
      ))
      explanation ++= explainAlongPath(a, c)
      explanation ++= explainAlongPath(b, c)
    }
    explanation.toSet
  }

  private def explainAlongPath(aL: Int, c: Int): ListBuffer[Formula] = {
    var explanation = new ListBuffer[Formula]
    var a = computeHighestNode(aL)
    while(a != c) {
      val b = proofStructure(a)
      //println("a: "+ a)
      //println("c: "+ c)
      //println(proofStructure.zip(proofLabels).mkString("\n", "\n", "\n"))
      proofLabels(a) match {
        case (eq@Equals(a: Variable, b: Variable), null) => explanation += eq
        case (Equals(fa@Apply(a1, a2), a: Variable),
              Equals(fb@Apply(b1, b2), b: Variable)) => {
          
          // TODO commenting this out breaks the explain test case
          //explanation += Equals(fa, a)
          //explanation += Equals(fb, b)

          pendingProofs.enqueue((termToId(a1), termToId(b1)))
          pendingProofs.enqueue((termToId(a2), termToId(b2)))
        }
        case _ => throw new Exception("Can't match edgeLabel "+ proofLabels(a))
      }
      // UNION
      eqClass(findEqClass(a)) = findEqClass(b)

      a = computeHighestNode(b)
    }
    explanation
  }

}

