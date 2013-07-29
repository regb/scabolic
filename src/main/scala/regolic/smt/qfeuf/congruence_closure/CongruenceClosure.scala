package regolic.smt.qfeuf

import regolic.smt.Solver
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.Trees.IntSort

import scala.collection.mutable.Queue
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.Set
import scala.collection.mutable.ListBuffer

object FastCongruenceSolver extends Solver {
  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  def isSat(f: Formula): Option[scala.collection.immutable.Map[FunctionSymbol, Term]] = {
    val And(fs) = f

    val eqs = Flattener(Currifier(fs.filter{x => x match {
      case Equals(t1, t2) => true
      case Not(Equals(t1, t2)) => false
      case _ => throw new Exception("Formula "+ x +" is not an equality")
    }}.asInstanceOf[List[PredicateApplication]]))

    val congruenceClosure = new CongruenceClosure(eqs)
    eqs.foreach(congruenceClosure.merge)

    // Are two variables, which shouldn't be equal congruent?
    val unsatTerms = fs.filter{
      case Not(Equals((t1: Variable), (t2: Variable))) if congruenceClosure.areCongruent(t1, t2) => true
      case _ => false
    }
    // For each of such equalities, get the reason
    unsatTerms.foreach{
      case Not(Equals((t1: Variable), (t2: Variable))) => congruenceClosure.explain(t1, t2)
      case _ => ()
    }

    if(unsatTerms.isEmpty) Some(scala.collection.immutable.Map()) else None
  }

}

/*
 * Representing the so-called proof forest
 */
class ProofStructureNode(val name: Term, var edgeLabel: Any) {
  var parent: ProofStructureNode = null

  def hasParent = parent != null

  override def toString = {
    val to = if(hasParent) " [=> "+ parent.name +"]" else ""
    name + to
  }
}

/*
 * Algorithm as described in "Fast congruence closure and extensions" by
 * Nieuwenhuis and Oliveras
 */
class CongruenceClosure(eqs: List[PredicateApplication]) {
  // TODO change Maps to Arrays where a Term.id is the index?
  // TODO collect EqClass stuff in separate object 

  def extractVariables(t: Term) = t match {
    case FunctionApplication(_, List((c1: Variable), (c2: Variable))) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
  private var elems: Set[Term] = Set() ++ eqs.foldRight(List.empty[Term])((eq, l) => eq match {
    case Equals(t1, t2) => extractVariables(t1) ::: extractVariables(t2) ::: l
    case _ => throw new Exception("Couldn't extract pair of terms from "+ eq)
  })
    
  private var node: Map[Term,ProofStructureNode] = Map() ++ elems.map{e => (e, new ProofStructureNode(e, None))}

  private var repr: Map[Term,Term] = Map() ++ elems.zip(elems)
    
  private val pending: Queue[Any] = Queue()

  private val useList = new HashMap[Term, Queue[PredicateApplication]] {
    override def default(k: Term) = {
      val v = Queue[PredicateApplication]()
      this += (k -> v)
      v
    }
  }

  private val lookup: Map[(Term, Term), Option[PredicateApplication]] = Map().withDefaultValue(None)

  private var classList: Map[Term, Queue[Term]] = Map() ++ elems.map(el => (el, Queue(el)))

  def merge(eq: PredicateApplication) {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pending.enqueue(eq)
        propagate()
      }
      case Equals(FunctionApplication(_, List(a1, a2)), a)  => {
        lookup(repr(a1),repr(a2)) match {
          case Some(f: PredicateApplication) => {
            pending enqueue (eq, f)
            propagate()
          }
          case _ => {
            lookup((repr(a1),repr(a2))) = Some(eq)
            useList(repr(a1)).enqueue(eq)
            useList(repr(a2)).enqueue(eq)
          }
        }
      }
    }
  }

  private def propagate() {
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
        }

        while(useList(oldreprA).nonEmpty) {
          val f1 = useList(oldreprA).dequeue()
          val Equals(FunctionApplication(_, List(c1, c2)),c) = f1

          lookup(repr(c1), repr(c2)) match {
            case Some(f2@Equals(FunctionApplication(_, List(d1, d2)), d)) => {
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
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => repr(c)
      case FunctionApplication(_, List(t1, t2)) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        lookup(u1, u2) match {
          case Some(Equals(_, a)) if (u1.isInstanceOf[Variable] &&
            u2.isInstanceOf[Variable]) => repr(a)
          case _ => FunctionApplication(applyFun, List(u1.asInstanceOf[Variable],
            u2.asInstanceOf[Variable]))
        }
      }
    }
  }

  def areCongruent(s: Term, t: Term): Boolean = {
    normalize(s) == normalize(t)
  }

  private val pendingProofs: Queue[PredicateApplication] = Queue()
  private var eqClass: Map[ProofStructureNode,ProofStructureNode] = Map() ++ node.values.zip(node.values)

  private def reverseEdges(from: ProofStructureNode) {
    @annotation.tailrec
    def nestedReverseEdges(curr: ProofStructureNode, next: ProofStructureNode) {
      if(curr.hasParent && next.hasParent) {
        val save = next.parent
        next.parent = curr
        nestedReverseEdges(next, save)
      } else if(curr.hasParent && !next.hasParent) {
        next.parent = curr
      }
    }
    if(from.hasParent) {
      val save = from.parent
      from.parent = null
      nestedReverseEdges(from, save)
    }
  }

  private def insertEdge(a: Variable, b: Variable, label: Any) = {
    val from = node(a)
    reverseEdges(from)
    from.parent = node(b)
    from.edgeLabel = label
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

  def explain(c1: Variable, c2: Variable) = {
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
    explanation.toList
  }

  private def explainAlongPath(aL: ProofStructureNode, c: ProofStructureNode) = {
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
          if(a1 != b1)
            pendingProofs.enqueue(Equals(a1, b1))
          if(a2 != b2)
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

