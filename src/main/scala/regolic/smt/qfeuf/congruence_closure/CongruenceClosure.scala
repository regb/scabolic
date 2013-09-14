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

object FastCongruenceSolver extends Solver {
  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  def isSat(f: Formula): Pair[Boolean, Option[collection.immutable.Map[Formula, Set[Formula]]]] = {
    val And(fs) = f

    val neqs = Map[Formula, Formula]()
    val transformedToEq: collection.immutable.Map[Formula, Formula] = fs.flatMap{
      case eq@Equals(_, _) => Flattener(Currifier(eq)).map(l => (l, eq))
      case Not(eq@Equals(_, _)) => {
        val eqs = Flattener(Currifier(eq))
        neqs(eqs.head) = eq
        eqs.tail.map(l => (l, eq))
      }
      case _ => None
    }.toMap
      
    val transformedEqs = transformedToEq.keySet
    val congruenceClosure = new CongruenceClosure
    congruenceClosure.initialize(transformedEqs)
    transformedEqs.foreach(congruenceClosure.merge)

    val unsatTerms = neqs.keys.filter{
      // Are two variables, which shouldn't be equal congruent?
      case Equals(t1, t2) if congruenceClosure.areCongruent(t1, t2) => true
      case _ => false
    }.toList

    // For each such inequality, get the explanation why it must be an equality
    val explanations: collection.immutable.Map[Formula, Set[Formula]] = unsatTerms.map{
      case eq@Equals((t1: Variable), (t2: Variable)) => (neqs(eq),
        congruenceClosure.explain(t1, t2).withFilter{
            /*
             * Only use equalities between variables
             */
            case Equals((v1: Variable), (v2: Variable)) => true
            case _ => false
          }.map(transformedToEq(_)))
    }.toMap

    if(unsatTerms.isEmpty)
      (true, None) // TODO what consequences to return for T-propagation?
    else
      (false, Some(explanations))
  }

}

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

  private val posLitList = new HashMap[Term, collection.mutable.Set[Formula]] {
    override def default(k: Term) = {
      val v = collection.mutable.Set[Formula]()
      this += (k -> v)
      v
    }
  }
  private val negLitList = new HashMap[Term, collection.mutable.Set[Formula]] {
    override def default(k: Term) = {
      val v = collection.mutable.Set[Formula]()
      this += (k -> v)
      v
    }
  }
  private var diseq = Map[Term, collection.mutable.Set[Pair[Timestamp,Term]]]()
  //private var diseq = new HashMap[Int, HashMap[Term, collection.mutable.Set[Formula]]] {
    //override def default(k: Int) = {
      //val v = new HashMap[Term, collection.mutable.Set[Formula]] {
        //override def default(k: Term) = {
          //val v = collection.mutable.Set[Formula]()
          //this += (k -> v)
          //v
        //}
      //}
      //this += (k -> v)
      //v
    //}
  //}
  //private var diseq = new HashMap[Term, collection.mutable.Set[Formula]] {
    //override def default(k: Term) = {
      //val v = collection.mutable.Set[Formula]()
      //this += (k -> v)
      //v
    //}
  //}

  var lookup: Map[(Term, Term), Pair[Timestamp, Option[Formula]]] = Map().withDefaultValue((new Timestamp(0,0), None))

  //var lookup = new HashMap[Int, Map[(Term, Term), Option[Formula]]] {
    //override def default(k: Int) = {
      //val v = Map[(Term, Term), Option[Formula]]().withDefaultValue(None)
      //this += (k -> v)
      //v
    //}
  //}
  
  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
    
  def initialize(ls: Set[Formula]) {//I.e. constructor
    val newElems = collection.mutable.Set[Term]()
    for(l <- ls) {
      l match {
        case Equals(t1, t2) => {
          newElems ++= extractVariables(t1)
          newElems ++= extractVariables(t2)
          if(t1.isInstanceOf[Variable] && t2.isInstanceOf[Variable]) {
            posLitList(t1) += l
            posLitList(t2) += l
            //negLitList(t1) += Not(l)
            //negLitList(t2) += Not(l)
          }
        }
        case Not(eq@Equals((t1: Variable), (t2: Variable))) => {
          // TODO we should check if the repr exists when we setTrue an
          // inequality and return an Error if not, rather than adding them for
          // all variables
          newElems ++= extractVariables(t1)
          newElems ++= extractVariables(t2)
          //posLitList(t1) += eq
          //posLitList(t2) += eq
          negLitList(t1) += l
          negLitList(t2) += l
        }
        case _ => ()
      }
    }
    newElems.foreach(e => {
        useList(e) = Queue[Formula]()
        diseq(e) = collection.mutable.Set[Pair[Timestamp, Term]]()
        repr(e) = e
        classList(e) = Queue(e)
        node(e) = new ProofStructureNode(e, null)
      })
    repr ++= newElems.map(e => (e, e))
    classList ++= newElems.map(el => (el, Queue(el)))
    node ++= newElems.map{e => (e, new ProofStructureNode(e, null))}
    elems ++= newElems
  }

  private val elems = collection.mutable.Set[Term]()

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
      classList(newRepr).dequeueFirst(_ == elem)
      classList(oldRepr).enqueue(elem)
    }
  }

  def isTrue(l: Formula) = { //I.e. areCongruent
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
  def backtrack(n: Int) = {
    //println("in tSolver backtrack: "+ iStack.mkString("\n", "\n", "\n"))
    //println("repr before backtracking: "+ repr.mkString("\n", "\n", "\n"))
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        val delTimestamp = new Timestamp(iStack.top._1, iStack.size)
        invalidTimestamps += delTimestamp

        //println("popping: "+ iStack.top._2)
        undoMerge(iStack.pop._2)
      }}

    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
    //println("t-backtracking done: "+ iStack.mkString("\n", "\n", "\n"))
  
    //println("t-backtracking done, invalid timestamps: "+ invalidTimestamps.mkString("\n", "\n", "\n"))
    //println("repr after backtracking: "+ repr.mkString("\n", "\n", "\n"))
    //println("diseq after backtracking: "+ diseq.mkString("\n", "\n", "\n"))
  }

  // l is t-consequence of setTrue(lPrime)
  def explain(l: Formula, lPrime: Formula): Set[Formula] = {
    assert(!iStack.isEmpty)
    //println("in explain, l: "+ l +", lPrime: "+ lPrime)
    
    // undo all merges after lPrime was pushed onto the iStack
    val restoreIStack = Stack[Pair[Int, Formula]]()
    val restoreEdgesStack = Stack[Pair[ProofStructureNode, ProofStructureNode]]()
    while(iStack.top._2 != lPrime) {
      val top = iStack.pop
      restoreIStack.push(top)
      if(iStack.isEmpty)
        throw new Exception("lPrime was not pushed to iStack")

      undoEdgesStack(top._2).foreach{case (from, reversedTo) => {
          // not storing edge label is fine as parent is null anyhow
          restoreEdgesStack.push((from, from.parent))
          removeEdge(from, reversedTo)
        }
      }
    }

    // actual explain computation
    val retVal = l match{
      case Equals((e1: Variable), (d1: Variable)) => {
        explain(e1, d1)
      }
      case Not(Equals((d1: Variable), (e1: Variable))) => {
        val cause = negReason(l)
        //println("cause:" + cause)
        val Not(Equals((d2: Variable), (e2: Variable))) = cause
        (explain(d1, d2) union explain(e1, e2)) + cause
      }
      case _ => throw new Exception("explain shouldn't be called on equalities containing functions")
    }

    // restore state before computing the explanation
    while(!restoreIStack.isEmpty) {
      val top = restoreIStack.pop
      iStack.push(top)
    }
    while(!restoreEdgesStack.isEmpty) {
      val (from, to) = restoreEdgesStack.pop
      makeEdge(from, to)
    }

    retVal
  }

  var node = Map[Term, ProofStructureNode]()

  private var repr = Map[Term, Term]()
    
  private val pending: Queue[Any] = Queue()

  private var useList = Map[Term, Queue[Formula]]()

  private var classList = Map[Term, Queue[Term]]()

  val iStack = new Stack[Pair[Int, Formula]]


  private val undoReprChangeStack = new HashMap[Formula, Stack[Tuple3[Term, Term, Term]]] {
    override def default(k: Formula) = {
      val v = Stack[Tuple3[Term, Term, Term]]()
      this += (k -> v)
      v
    }
  }
 
  var negReason = Map[Formula, Formula]()

  var trigger: Formula = null

  class Timestamp(private val height: Int, private val ctr: Int) {
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
  private def currentTimestamp: Timestamp = new Timestamp(iStack.size, ctr)
  private var ctr: Int = 0

  // Every call to setTrue needs to push a literal to the iStack, so that
  // backtracking is possible for each T-literal enqueued in the DPLL engine
  def setTrue(l: Formula): Option[Set[Formula]] = {
    //println("setTrue: "+ l)
    trigger = l
    ctr += 1
    iStack.push((ctr, l))

    val retVal = l match {
      case eq@Equals(t1, t2) => {
        //merge(eq)
        val tmp = merge(eq)
        tmp match {
          case None => None
          case _ => Some(Set.empty[Formula])
        }
      }
      case Not(Equals(t1: Variable, t2: Variable)) => {
        if(!areCongruent(t1, t2)) {
          //Diseq, a hash table containing all currently true disequalities between
          //representatives
          diseq(repr(t1)) += Pair(currentTimestamp, repr(t2))
          diseq(repr(t2)) += Pair(currentTimestamp, repr(t1))

          // Computing the T-consequences
          val (a, b) = (repr(t1), repr(t2))
          val (cla, clb) = (classList(a), classList(b))
          val cl = if(cla.size < clb.size) cla else clb
          val tConsequence = ListBuffer[Formula]()
          for(c <- cl) {
            tConsequence ++= negLitList(c).filter{
              case Not(Equals(t1, t2)) => {
                (repr(t1) == a && repr(t2) == b) ||
                (repr(t1) == b && repr(t2) == a) 
              }
            }
          }

          negReason ++= tConsequence.map(ineq => (ineq, l))
          //Some(tConsequence.toSet)
          Some(Set.empty[Formula])
        } else
          None // inconsistent
      }
      case _ => throw new Exception("Unsupported formula. Maybe SetTrue of an inequality containing a function?")
    }

    //println("iStack before pushing "+ l +":"+ iStack.mkString("\n", "\n", "\n"))
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
        pending.enqueue(eq)
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        lookup(repr(a1),repr(a2)) match {
          case (timestamp, Some(eq2@Equals(Apply(_, _), _))) if timestamp.isValid => {
            pending.enqueue((eq, eq2))
            propagate()
          }
          case _ => {
            lookup((repr(a1), repr(a2))) = (currentTimestamp, Some(eq))
            useList(repr(a1)).enqueue(eq)
            useList(repr(a2)).enqueue(eq)
            Some(Set.empty[Formula]) // no new unions, no T-consequences
          }
        }
      }
    }
  }
  
  private def propagate(): Option[Set[Formula]] = {
    val tConsequence = ListBuffer[Formula]()
    while(pending.nonEmpty) {
      val e = pending.dequeue()
      
      val p = e match {
        case Equals(a: Variable, b: Variable) => (a, b)
        case (Equals(_, a: Variable), Equals(_, b: Variable)) => (a, b)
      }
      val (a, b) = if(classList(repr(p._1)).size > classList(repr(p._2)).size){
        p.swap
      } else p

      // merge classes of a and b (a => b)
      if(repr(a) != repr(b)) {

        //println("repr("+ a +"): "+ repr(a))
        //println("repr("+ b +"): "+ repr(b))
        //println("--diseq: "+ diseq.mkString("\n", "\n", "\n"))
        // trying to merge classes, which are disequal
        if(diseq(repr(a)).exists{case(t,v) => {t.isValid && v == repr(b)}}) {
          // If for some reason, the trigger literal causing this inconsistency
          // is not pushed onto the I-stack, make sure to set the timestamp
          // invalid here.
          // As it stands now, it gets taken care of in backtrack.
          //println(trigger +" is inconsistent because of "+ repr(a) +" != "+
            //diseq(repr(a)).filter{case(t,v) => {t.isValid && v == repr(b)}})
          //println(repr(a) +" = "+ a +" because of: "+explain(repr(a).asInstanceOf[Variable], a))
          //println(repr(b) +" = "+ b +" because of: "+ explain(repr(b).asInstanceOf[Variable], b))
          return None
        }

        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        assert(classList(oldreprA).nonEmpty)
        while(classList(oldreprA).nonEmpty) {
          val c = classList(oldreprA).dequeue()
          /*
           *If a positive SetTrue, and its subsequent congruence closure, produces a
           *union such that a class with former representative a is now represented by a
           *different b, then, for each a in the class list of a, the positive literal list of a is
           *traversed and all a=b in this list are returned as T-consequences. Also the nega-
           *tive literal list of all such a is traversed, returning those a' !=
           *c' such that a != c is stored in Diseq, a hash table containing all
           *currently true disequalities between representatives; analogously
           *also the negative literal list of all b is traversed.
           */

          tConsequence ++= posLitList(c).filter{
            case Equals(t1, t2) => (repr(t1) == oldreprA && repr(t2) == repr(b)) || (repr(t1) == repr(b) && repr(t2) == oldreprA)
          }
          tConsequence ++= negLitList(c).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              if(diseq(repr(t1)).exists{case (t,v) => {t.isValid && v == repr(t2)}}) {
                negReason(ineq) = Not(Equals(repr(t1), repr(t2)))
                true
              } else {
                false
              }
            }
          }}

          undoReprChangeStack(trigger).push((c, repr(c), repr(b)))
          repr(c) = repr(b)
          classList(repr(b)).enqueue(c)
        }

        // update disequalities
        diseq(oldreprA).foreach{d => d match {
          case (t,v) if t.isValid => {
            diseq(repr(b)) += Pair(currentTimestamp, v)
            diseq(v) ++= diseq(v).map{pair => {
                pair match {
                  case (t,r) if t.isValid => (currentTimestamp, repr(r))
                  case _ => pair
                }
              }
            }
          }
          case _ => ()
        }}
        // TODO maybe just completely clear diseq(oldreprA). invalid timestamps
        // aren't needed and valid ones are moved
        diseq(oldreprA) = diseq(oldreprA).filter{case (t,_) => t.isValid}
        //diseq(oldreprA).clear
        //(currentTimestamp, collection.mutable.Set.empty[Term])

        while(useList(oldreprA).nonEmpty) {
          val f1 = useList(oldreprA).dequeue()
          val Equals(Apply(c1, c2),c) = f1

          lookup(repr(c1), repr(c2)) match {
            case (timestamp, Some(f2@Equals(Apply(d1, d2), d))) if timestamp.isValid => {
              pending.enqueue((f1, f2))
            }
            case _ => {
              lookup((repr(c1), repr(c2))) = (currentTimestamp, Some(f1))

              useList(repr(b)).enqueue(f1)
            }
          }
        }
      }
      assert(repr(a) == repr(b))
    }
    Some(tConsequence.toSet)
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => repr.getOrElse(c, c)
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        lookup(u1, u2) match {
          case (timestamp, Some(Equals(Apply(_, _), a))) if (u1.isInstanceOf[Variable] &&
            u2.isInstanceOf[Variable]) && timestamp.isValid => repr.getOrElse(a, a)
          case _ => Apply(u1.asInstanceOf[Variable], u2.asInstanceOf[Variable])
        }
      }
    }
  }

  def areCongruent(s: Term, t: Term): Boolean = {
    //println(s +" => "+ normalize(s))
    //println(t +" => "+ normalize(t))
    //println()
    normalize(s) == normalize(t)
  }

  private val pendingProofs: Queue[Formula] = Queue()
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
  
  private def insertEdge(a: Variable, b: Variable, label: Any) = {
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

  def nearestCommonAncestor(a: Term, b: Term): Option[ProofStructureNode] = {
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

  def explain(c1: Variable, c2: Variable): Set[Formula] = {
    //println("Explaining why "+ c1 +" = "+ c2)
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    // reset makes explanations complete, but is it necessary?
    eqClass.clear()
    eqClass ++= node.values.zip(node.values)

    var explanation = new ListBuffer[Formula]
    pendingProofs.enqueue(Equals(c1, c2))
    while(pendingProofs.nonEmpty) {
      val Equals(a, b) = pendingProofs.dequeue()
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
        case Equals(a: Variable, b: Variable) => explanation += Equals(a, b)
        case (Equals(fa@FunctionApplication(_, List(a1, a2)), a: Variable),
          Equals(fb@FunctionApplication(_, List(b1, b2)), b: Variable)) => {
          
          // Map explanation back
          // TODO uncommenting this breaks the explain test case
          explanation += Equals(fa, a)
          explanation += Equals(fb, b)

          pendingProofs.enqueue(Equals(a1, b1))
          pendingProofs.enqueue(Equals(a2, b2))
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

