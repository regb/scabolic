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
  
  /*
   * Representing the so-called proof forest
   * TODO the graph should be represented by an Int array as described in the
   * paper, but need proper optimization work first
   */
  private var proofStructure: Array[Int] = null
  private var proofLabels: Array[Int] = null
  class ProofStructureNode(val name: Term, var edgeLabel: Any) {
    var parent: ProofStructureNode = null

    def hasParent = parent != null

    override def toString = {
      val to = if(hasParent) " -> "+ parent.name +" [label=\""+ edgeLabel +"\"]" else ""
      name + to +";"
    }
  }

  // TODO change Maps to Arrays where a Term.id is the index?
  // TODO collect EqClass stuff in separate object
  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  private var posLitList: Array[Array[Formula]] = null
  private var negLitList: Array[Array[Formula]] = null

  private var diseq: Array[ListBuffer[Tuple3[Timestamp,Int,Formula]]] = null

  val lookup: Map[(Int, Int), Pair[Timestamp, Formula]] = Map()//.withDefaultValue((new Timestamp(0,0), null))

  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
    
  private val termToId = Map[Term, Int]()
  private var idToTerm: Array[Term] = null

  private var eqToTerms: Array[Pair[Int,Int]] = null
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
        case _ => ()
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

    node = new Array(numTerms)

    idToTerm = new Array(numTerms)

    var id = -1
    for(t <- terms) {
      id += 1
      termToId += (t -> id)
      idToTerm(id) = t

      repr(id) = id
      classList(id) = ListBuffer()
      classList(id) += id
      useList(id) = ListBuffer()
      diseq(id) = ListBuffer()

      proofStructure(id) = id
      proofLabels(id) = -1
      node(id) = new ProofStructureNode(t, null)

      
      posLitList(id) = pos(t).toArray
      negLitList(id) = neg(t).toArray
    }
  }

  def undoMerge(l: Formula) {
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
      val (elem, oldRepr, newRepr) = undoReprChangeStack(l).pop
      repr(elem) = oldRepr
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


  val invalidTimestamps = collection.mutable.Set[Timestamp]()
  def backtrack(n: Int) {
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        val (topCtr, topTrigger) = iStack.pop
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        //println("invalidating timestamp "+ delTimestamp)
        invalidTimestamps += delTimestamp

        //println("popping: "+ topTrigger)
        //println("delTimestamp: "+ delTimestamp)
        undoMerge(topTrigger)
      }}

      pending.clear()

    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
    currentTimestamp = new Timestamp(iStack.size, ctr)
  }

  def backtrackTo(l: Formula) {
    //println("istack: "+ iStack.mkString("\n", "\n", "\n"))
    if(l != null) {
      var tmp: Formula = null
      do {
        val (topCtr, topTrigger) = iStack.pop
        tmp = topTrigger
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        //println("invalidating timestamp "+ delTimestamp)
        invalidTimestamps += delTimestamp

        //println("popping: "+ topTrigger)
        //println("delTimestamp: "+ delTimestamp)
        undoMerge(topTrigger)

        if(iStack.isEmpty)
          throw new Exception(l +" was not pushed to iStack")
      } while(tmp != l) 

      pending.clear()
    }
    currentTimestamp = new Timestamp(iStack.size, ctr)
  }

  // l is t-consequence of setTrue(lPrime)
  def explain(l: Formula, lPrime: Formula = null): Set[Formula] = {
    //println("in explain, l: "+ l +", lPrime: "+ lPrime)
    
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
        val cause = diseq(repr(termToId(d1))).find{case (t,elem,_) => t.isValid && elem == repr(termToId(e1))}.get._3
        //println("cause: "+ cause)

        val Not(Equals((d2: Variable), (e2: Variable))) = cause
        // Checking for 1 congruence is enough. If d1 congruent e2 as well, that
        // would mean that d1 = d2 AND d1 = e2 AND d2 != e2, which is
        // inconsistent
        val d1Id = termToId(d1)
        val d2Id = termToId(d2)
        val e1Id = termToId(e1)
        val e2Id = termToId(e2)
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

  var node: Array[ProofStructureNode] = null

  private var repr: Array[Int] = null
    
  private val pending: Queue[Pair[Formula, Formula]] = Queue()

  // We need to be able to both append and prepend (when backtracking), which a
  // queue does not support 
  private var useList: Array[ListBuffer[Formula]] = null

  private var classList: Array[ListBuffer[Int]] = null

  val iStack = new Stack[Pair[Int, Formula]]


  private val undoReprChangeStack = new HashMap[Formula, Stack[Tuple3[Int, Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Tuple3[Int, Int, Int]]()
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
 
  var negReason = Map[Formula, Formula]()

  var trigger: Formula = null

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
  private var currentTimestamp: Timestamp = null
  private var ctr: Int = 0

  // Every call to setTrue needs to push a literal to the iStack, so that
  // backtracking is possible for each T-literal enqueued in the DPLL engine
  def setTrue(l: Formula): Option[Set[Formula]] = {
    //println("setTrue: "+ l +" h: "+ iStack.size)
    trigger = l
    ctr += 1
    iStack.push((ctr, l))
    reason = null
    currentTimestamp = new Timestamp(iStack.size, ctr)

    //if((l & 1) == 0) {
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
          val t1Id = termToId(t1)
          val t2Id = termToId(t2)
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
                val s1Id = termToId(s1)
                val s2Id = termToId(s2)
                (repr(s1Id) == a && repr(s2Id) == b) ||
                (repr(s1Id) == b && repr(s2Id) == a) 
              }
            }
          }

          negReason ++= tConsequence.map(ineq => (ineq, l))
          //println("negReason: "+ negReason.mkString("\n", "\n", "\n"))
          //Some(tConsequence.toSet)
          Some(Set.empty[Formula])
        } else {
          reason = Equals(t1, t2)
          None // inconsistent
        }
      }
    }

    //println("iStack before pushing "+ l +":"+ iStack.mkString("\n", "\n", "\n"))

    //if(retVal == None)
      //backtrack(1)

    //if(retVal != None)
      //println("t-consequences: "+ retVal.get.mkString("\n", "\n", "\n"))
    //else
      //println("inconsistency detected")
    //println("after setTrue("+ l +"): "+ repr.mkString("\n", "\n", "\n"))
    //println("repr: "+ repr.mkString("\n", "\n", "\n"))
    //println("diseq: "+ diseq.mkString("\n", "\n", "\n"))
    //println("lookup: "+ lookup.mkString("\n", "\n", "\n"))

    retVal
  }

  def merge(eq: Formula): Option[Set[Formula]] = {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pending.enqueue((eq, null))
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        val a1Id = termToId(a1)
        val a2Id = termToId(a2)
        lookup(repr(a1Id),repr(a2Id)) match {
          case (timestamp, eq2@Equals(Apply(_, _), _)) if timestamp.isValid => {
            pending.enqueue((eq, eq2))
            propagate()
          }
          case (timestamp, _) => {
            // all equalities containing apply are merged at the beginning and
            // there should never be backtracking, so the timestamp stays valid.
            //assert(timestamp.isValid)

            lookup += ((repr(a1Id), repr(a2Id)) -> (currentTimestamp, eq))
            useList(repr(a1Id)).append(eq)
            useList(repr(a2Id)).append(eq)
            Some(Set.empty[Formula]) // no new unions, no T-consequences
          }
        }
      }
    }
  }

  var reason: Formula = null
  
  private def propagate(): Option[Set[Formula]] = {
    val tConsequence = ListBuffer[Formula]()
    while(pending.nonEmpty) {
      val e = pending.dequeue()
      
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
        if(diseq(repr(a)).exists{case(t,v,_) => {t.isValid && v == repr(b)}}) {
          // If for some reason, the trigger literal causing this inconsistency
          // is not pushed onto the I-stack, make sure to set the timestamp
          // invalid here.
          // As it stands now, it gets taken care of in backtrack.
          reason = Not(e._1)
          return None
        }

        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        for(c <- classList(oldreprA)) {
          tConsequence ++= posLitList(c).filter{
            case Equals(t1, t2) => {
              val t1Id = termToId(t1)
              val t2Id = termToId(t2)
              (repr(t1Id) == oldreprA && repr(t2Id) == repr(b)) || (repr(t1Id) == repr(b) && repr(t2Id) == oldreprA)
            }
          }

          undoReprChangeStack(trigger).push((c, repr(c), repr(b)))
          repr(c) = repr(b)
          classList(repr(b)).append(c)
        }
        classList(oldreprA).clear()

        // update disequalities
        diseq(oldreprA).foreach{d => d match {
          case (t,v,reason1) if t.isValid => {
            diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)

            diseq(v) ++= diseq(v).map{triple => {
                triple match {
                  case (t,r,reason2) if t.isValid => (currentTimestamp, repr(r), reason2)
                  case _ => triple
                }
              }
            }
          }
          case _ => ()
        }}
        // try to do this more compactly in loop, but need to take care that
        // iteration isn't affected (how robust is iterator?)
        diseq(oldreprA).filterNot{case (t,_,_) => t.isValid}

        for(aP <- classList(oldreprA)) {
          tConsequence ++= negLitList(aP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1)
              val t2Id = termToId(t2)
              diseq(oldreprA).exists{case (t,v,_) => t.isValid && (v == repr(t1Id) || v == repr(t2Id))}
            }
          }}
        }

        for(bP <- classList(repr(b))) {
          tConsequence ++= negLitList(bP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1)
              val t2Id = termToId(t2)
              diseq(repr(b)).exists{case (t,v,_) => t.isValid && (v == repr(t1Id) || v == repr(t2Id))}
            }
          }}
        }

        for(f1 <- useList(oldreprA)) {
          val Equals(Apply(c1, c2),_) = f1

          val c1Id = termToId(c1)
          val c2Id = termToId(c2)
          lookup(repr(c1Id), repr(c2Id)) match {
            case (timestamp, f2@Equals(Apply(_, _),_)) if timestamp.isValid => {
              undoUseListStack(trigger).push(Tuple3(f1, oldreprA, -1))
              pending.enqueue((f1, f2))
            }
            case (timestamp, _) => {
              lookup += ((repr(c1Id), repr(c2Id)) -> (currentTimestamp, f1))

              undoUseListStack(trigger).push(Tuple3(f1, oldreprA, repr(b)))
              useList(repr(b)).append(f1)
            }
          }
        }
        useList(oldreprA).clear()
      } // if
    } // while
    Some(tConsequence.toSet)
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => {
        if(termToId.contains(c)) idToTerm(repr(termToId(c))) else c
      }
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        lookup(termToId(u1), termToId(u2)) match {
          case (timestamp, Equals(_,a)) if u1.isInstanceOf[Variable] &&
            u2.isInstanceOf[Variable] && timestamp.isValid => {
            if(termToId.contains(a)) idToTerm(repr(termToId(a))) else a
          }
          case _ => Apply(u1, u2)
        }
      }
    }
  }

  def areCongruent(t1: Term, t2: Term): Boolean = {
    normalize(t1) == normalize(t2)
  }

  private val pendingProofs: Queue[Pair[Int,Int]] = Queue()
  private val eqClass: Map[ProofStructureNode,ProofStructureNode] = Map()

  private def reverseEdges(from: ProofStructureNode) = {
    var p = from
    var q: ProofStructureNode = null
    var r: ProofStructureNode = null
    var qEdge: Any = null
    var rEdge: Any = null

    while(p != null) {
      r = q
      q = p
      p = q.parent

      rEdge = qEdge
      qEdge = q.edgeLabel

      q.parent = r
      q.edgeLabel = rEdge
    }
    from.parent = null
    q
  }

  private val undoEdgesStack = new HashMap[Formula, Stack[Pair[ProofStructureNode, ProofStructureNode]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[ProofStructureNode, ProofStructureNode]]()
      this += (k -> v)
      v
    }
  }

  // removes the edge from to from.parent and reverses the edges in order to
  // restore the state before the edge was inserted (mind the order of edge insertions)
  private def removeEdge(from: ProofStructureNode, reversedTo: ProofStructureNode) {
    // not clearing edge label is fine as parent is null anyhow
    from.parent = null
    reverseEdges(reversedTo)
  }
  
  private def makeEdge(from: ProofStructureNode, to: ProofStructureNode, label: Any = null): ProofStructureNode =  {
    val retVal = reverseEdges(from)
    from.parent = to
    if(label != null)
      from.edgeLabel = label
    retVal
  }
  
  private def insertEdge(a: Int, b: Int, label: Any) = {
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    val from = node(a)
    val reversedTo = makeEdge(node(a), node(b), label)

    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    //println("inserted "+ a +" -> "+ b +" repr a: "+ repr(a) +", repr b: "+ repr(b))
    undoEdgesStack(trigger).push((from, reversedTo))
  }
  
  private def findEqClass(x: ProofStructureNode): ProofStructureNode = {
    if(eqClass(x) == x)
      x
    else
      findEqClass(eqClass(x))
  }

  private def computeHighestNode(c: ProofStructureNode): ProofStructureNode = {
    @annotation.tailrec
    def nestedComputeHighestNode(x: ProofStructureNode): ProofStructureNode = {
      if(!x.hasParent || findEqClass(x.parent) != findEqClass(c)) 
        x
      else
        nestedComputeHighestNode(x.parent)
    }
    nestedComputeHighestNode(c)
  }

  def nearestCommonAncestor(a: Int, b: Int): Option[ProofStructureNode] = {
    @annotation.tailrec
    def pathToRoot(n: ProofStructureNode, acc: List[ProofStructureNode] =
      Nil): List[ProofStructureNode] = {
      //println("n: "+ n.name +", "+ acc.length)
      if(n.hasParent)
        pathToRoot(n.parent, n :: acc)
      else
        n :: acc // Include root
    }

    // TODO some overhead due to functional implemenation
    val commonPath = pathToRoot(node(a)).zip(pathToRoot(node(b))).filter{
      case (first, second) => first == second
    }
    if(commonPath.isEmpty)
      None
    else
      Some(commonPath.reverse.head._1)
  }

  def explain(c1: Int, c2: Int): Set[Formula] = {
    //println("Explaining why "+ c1 +" = "+ c2)
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    // reset makes explanations complete, but is it necessary?
    eqClass.clear()
    eqClass ++= node.map(n => (n, n))

    var explanation = new ListBuffer[Formula]
    pendingProofs.enqueue((c1, c2))
    while(pendingProofs.nonEmpty) {
      val (a, b) = pendingProofs.dequeue()
      val c = computeHighestNode(findEqClass(
        nearestCommonAncestor(a, b) match {
          case Some(x) => x
          case None => throw new Exception("No common ancestor "+ (a,b))
        }
      ))
      explanation ++= explainAlongPath(node(a), c)
      explanation ++= explainAlongPath(node(b), c)
    }
    //println("explanation: "+ explanation.mkString("\n", "\n", "\n"))
    explanation.toSet
  }

  private def explainAlongPath(aL: ProofStructureNode, c: ProofStructureNode): ListBuffer[Formula] = {
    var explanation = new ListBuffer[Formula]
    var a = computeHighestNode(aL)
    while(a.name != c.name) {
      val b = a.parent
      a.edgeLabel match {
        case (eq@Equals(a: Variable, b: Variable), null) => explanation += eq
        case (Equals(fa@Apply(a1, a2), a: Variable),
              Equals(fb@Apply(b1, b2), b: Variable)) => {
          
          // Map explanation back
          // TODO uncommenting this breaks the explain test case
          //explanation += Equals(fa, a)
          //explanation += Equals(fb, b)

          pendingProofs.enqueue((termToId(a1), termToId(b1)))
          pendingProofs.enqueue((termToId(a2), termToId(b2)))
        }
        case _ => throw new Exception("Can't match edgeLabel "+ a.edgeLabel)
      }
      // UNION
      eqClass(findEqClass(a)) = findEqClass(b)

      a = computeHighestNode(b)
    }
    explanation
  }

}

