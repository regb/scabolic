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
import scala.collection.mutable.Set
import scala.collection.mutable.ListBuffer

object FastCongruenceSolver extends Solver {
  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  def isSat(f: Formula): Pair[Boolean, Option[collection.immutable.Map[Formula, List[Formula]]]] = {
    val And(fs) = f

    val neqs = Map[PredicateApplication, PredicateApplication]()
    val transformedToEq: collection.immutable.Map[PredicateApplication, PredicateApplication] = fs.flatMap{
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
    congruenceClosure.initialize(transformedEqs.asInstanceOf[collection.immutable.Set[Formula]])
    transformedEqs.foreach(congruenceClosure.merge)

    val unsatTerms = neqs.keys.filter{
      // Are two variables, which shouldn't be equal congruent?
      case Equals(t1, t2) if congruenceClosure.areCongruent(t1, t2) => true
      case _ => false
    }.toList

    // For each such inequality, get the explanation why it must be an equality
    val explanations: collection.immutable.Map[PredicateApplication, collection.immutable.Set[PredicateApplication]] = unsatTerms.map{
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
      (false, Some(explanations.asInstanceOf[collection.immutable.Map[Formula, List[Formula]]]))
  }

}

/*
 * Representing the so-called proof forest
 */
class ProofStructureNode(val name: Term, var edgeLabel: Any) {
  var parent: ProofStructureNode = null

  def hasParent = parent != null

  override def toString = {
    val to = if(hasParent) " -> "+ parent.name +" [label=\""+ edgeLabel +"\"]" else ""
    name + to +";"
  }
}

/*
 * Algorithm as described in "Fast congruence closure and extensions" by
 * Nieuwenhuis and Oliveras
 */
class CongruenceClosure extends TheorySolver {
  // TODO change Maps to Arrays where a Term.id is the index?
  // TODO collect EqClass stuff in separate object
  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  private val posLitList = new HashMap[Term, Set[Formula]] {
    override def default(k: Term) = {
      val v = Set[Formula]()
      this += (k -> v)
      v
    }
  }
  private val negLitList = new HashMap[Term, Set[Formula]] {
    override def default(k: Term) = {
      val v = Set[Formula]()
      this += (k -> v)
      v
    }
  }
  private var diseq = new HashMap[Term, Set[Formula]] {
    override def default(k: Term) = {
      val v = Set[Formula]()
      this += (k -> v)
      v
    }
  }

  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
    
  def initialize(ls: collection.immutable.Set[Formula]) {//I.e. constructor
    for(l <- ls) {
      l match {
        case Equals((c1: Variable), (c2: Variable)) => {
          posLitList(c1) += l
          posLitList(c2) += l
          elems ++= extractVariables(c1)
          elems ++= extractVariables(c2)
        }
        case Not(Equals((c1: Variable), (c2: Variable))) => {
          negLitList(c1) += l
          negLitList(c2) += l
        }
      }
    }
  }

  private val elems = Set[Term]()

  def undoMerge(l: Formula) {
    while(!undoStack(l).isEmpty) {
      val (from, reversedTo) = undoStack(l).pop
      from.parent = null
      reverseEdges(reversedTo)
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
  def backtrack(n: Int) = {
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        val l = iStack.pop.l
        undoMerge(l)
      }}

      val s = iStack.top
      repr = s.repr
      classList = s.classList
      useList = s.useList
      lookup = s.lookup
      diseq = s.diseq
    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
  }

  def explain(l: Formula): collection.immutable.Set[Formula] = {
    l match{
      case Equals((e1: Variable), (d1: Variable)) => {
        explain(e1, d1).asInstanceOf[collection.immutable.Set[Formula]]
      }
      case Not(Equals((d1: Variable), (e1: Variable))) => {
        val cause = negTable(l)
        val Not(Equals((d2: Variable), (e2: Variable))) = cause
        (explain(d1, d2) union explain(e1, e2)).asInstanceOf[collection.immutable.Set[Formula]] + cause
      }
      case _ => throw new Exception("explain shouldn't be called on equalities containing functions")
    }
  }

  val node = Map[Term, ProofStructureNode]() ++ elems.map{e => (e, new ProofStructureNode(e, null))}

  private var repr = Map[Term,Term]() ++ elems.map(e => (e, e))
    
  private val pending: Queue[Any] = Queue()

  private var useList = new HashMap[Term, Queue[PredicateApplication]] {
    override def default(k: Term) = {
      val v = Queue[PredicateApplication]()
      this += (k -> v)
      v
    }
  }

  var lookup: Map[(Term, Term), Option[PredicateApplication]] = Map().withDefaultValue(None)

  private var classList = Map[Term, Queue[Term]]() ++ elems.map(el => (el, Queue(el)))

  val iStack = new Stack[State]

  class State(val l: Formula, val repr: Map[Term, Term], val classList:
    Map[Term, Queue[Term]], val useList: HashMap[Term,
    Queue[PredicateApplication]], val lookup: Map[(Term, Term),
    Option[PredicateApplication]], val diseq: HashMap[Term, Set[Formula]])

  var trigger: Formula = null

  var negTable = Map[Formula, Formula]()
  def setTrue(l: Formula): collection.immutable.Set[Formula] = {
    trigger = l
    l match {
      case eq@Equals(t1, t2) => {
        if(diseq.values.exists(_ == Not(l))) { // TODO inconsistent 
          throw new Exception("Inconsistent: "+ (t1, t2) +" are unequal.")
        } else {
          val tConsequence = merge(eq)

          // TODO how slow is cloning?
          iStack.push(new State(l, repr.clone, classList.clone, useList.clone, lookup.clone, diseq.clone))
          tConsequence
        }
      }
      case Not(Equals(t1, t2)) => {
        if(areCongruent(t1, t2)) { // TODO inconsistent
          throw new Exception("Inconsistent: "+ (t1, t2) +" are congruent.")
        } else {
          diseq(t1) += l
          diseq(t2) += l
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

          // TODO how slow is cloning?
          iStack.push(new State(l, repr.clone, classList.clone, useList.clone, lookup.clone, diseq.clone))
          negTable ++= tConsequence.map(ineq => (ineq, l))
          tConsequence.toSet
        }
      }
      case _ => throw new Exception("Unsupported formula")
    }
  }

  def merge(eq: PredicateApplication): collection.immutable.Set[Formula] = {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pending.enqueue(eq)
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        lookup(repr(a1),repr(a2)) match {
          case Some(eq2@Equals(Apply(_, _), _)) => {
            pending.enqueue((eq, eq2))
            propagate()
          }
          case _ => {
            lookup((repr(a1), repr(a2))) = Some(eq)
            useList(repr(a1)).enqueue(eq)
            useList(repr(a2)).enqueue(eq)
            collection.immutable.Set.empty[Formula] // no new unions, no T-consequences
          }
        }
      }
    }
  }
  
  private def propagate(): collection.immutable.Set[Formula] = {
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

      if(repr(a) != repr(b)) {
        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        while(classList(oldreprA).nonEmpty) {
          val c = classList(oldreprA).dequeue()
          repr(c) = repr(b)
          classList(repr(b)).enqueue(c)

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
              if(diseq(repr(t1)).contains(Not(Equals(repr(t1), repr(t2))))) {
                negTable(ineq) = Not(Equals(repr(t1), repr(t2)))
                true
              } else if(diseq(repr(t1)).contains(Not(Equals(repr(t2), repr(t1))))) {
                negTable(ineq) = Not(Equals(repr(t2), repr(t1)))
                true
              } else {
                false
              }
            }
          }}
        }

        while(useList(oldreprA).nonEmpty) {
          val f1 = useList(oldreprA).dequeue()
          val Equals(Apply(c1, c2),c) = f1

          lookup(repr(c1), repr(c2)) match {
            case Some(f2@Equals(Apply(d1, d2), d)) => {
              pending.enqueue((f1, f2))
            }
            case _ => {
              lookup((repr(c1), repr(c2))) = Some(f1)

              useList(repr(b)).enqueue(f1)
            }
          }
        }
      }
    }
    tConsequence.toSet
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => repr.getOrElse(c, c)
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        lookup(u1, u2) match {
          case Some(Equals(Apply(_, _), a)) if (u1.isInstanceOf[Variable] &&
            u2.isInstanceOf[Variable]) => repr.getOrElse(a, a)
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

  private val pendingProofs: Queue[PredicateApplication] = Queue()
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

  private val undoStack = new Map[Formula, Stack[Pair[ProofStructureNode,
  ProofStructureNode]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[ProofStructureNode, ProofStructureNode]]()
      this += (k -> v)
      v
    }
  }
  
  private def insertEdge(a: Variable, b: Variable, label: Any) = {
    val from = node(a)
    val reversedTo = reverseEdges(from)
    from.parent = node(b)
    from.edgeLabel = label
    undoStack(trigger).push((from, reversedTo))
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

  def explain(c1: Variable, c2: Variable): collection.immutable.Set[PredicateApplication] = {
    //println("Explaining why "+ c1 +" = "+ c2)
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    // reset makes explanations complete, but is it necessary?
    eqClass.clear()
    eqClass ++= node.values.zip(node.values)

    var explanation = new ListBuffer[PredicateApplication]
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

  private def explainAlongPath(aL: ProofStructureNode, c: ProofStructureNode): ListBuffer[PredicateApplication] = {
    var explanation = new ListBuffer[PredicateApplication]
    var a = computeHighestNode(aL)
    while(a.name != c.name) {
      val b = a.parent
      a.edgeLabel match {
        case Equals(a: Variable, b: Variable) => explanation += Equals(a, b)
        case (Equals(fa@FunctionApplication(_, List(a1, a2)), a: Variable),
          Equals(fb@FunctionApplication(_, List(b1, b2)), b: Variable)) => {
          
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

