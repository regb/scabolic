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

  def isSat(f: Formula): Pair[Boolean, Option[collection.immutable.Map[Formula, List[Formula]]]] = {
    val And(fs) = f

    val transformedToEq = collection.immutable.Map() ++ fs.flatMap{
      case eq@Equals(t1, t2) => Flattener(Currifier(eq)).map(l => (l, eq))
      case _ => None
    }
    val transformedEqs = transformedToEq.keySet.toList
    val congruenceClosure = new CongruenceClosure(transformedEqs)
    transformedEqs.foreach(congruenceClosure.merge)

    val unsatTerms = fs.flatMap{
      case Not(eq@Equals(_, _)) => Flattener(Currifier(eq))
      case _ => None
    }.filter{
      // Are two variables, which shouldn't be equal congruent?
      case Equals(t1, t2) if congruenceClosure.areCongruent(t1, t2) => true
      case _ => false
    }

    // For each such inequality, get the explanation why it must be an equality
    val explanations = collection.immutable.Map[Formula, List[Formula]]() ++ unsatTerms.map{
      case eq@Equals((t1: Variable), (t2: Variable)) => (eq,
        congruenceClosure.explain(t1, t2).withFilter{
            /*
             * Only use equalities between variables
             */
            case Equals((v1: Variable), (v2: Variable)) => true
            case _ => false
          }.map(transformedToEq(_)))
    }

    if(unsatTerms.isEmpty)
      (true, None)
    else
      (false, Some(explanations))
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
class CongruenceClosure(eqs: List[PredicateApplication]) {
  // TODO change Maps to Arrays where a Term.id is the index?
  // TODO collect EqClass stuff in separate object

  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
  private val elems: collection.immutable.Set[Term] = {
    val lb = new ListBuffer[Term]()
    for(Equals(t1, t2) <- eqs) {
      lb ++= extractVariables(t1)
      lb ++= extractVariables(t2)
    }
    lb.toSet
  }
    
  val node: Map[Term,ProofStructureNode] = Map() ++ elems.map{e => (e, new ProofStructureNode(e, null))}

  private val repr: Map[Term,Term] = Map() ++ elems.zip(elems)
    
  private val pending: Queue[Any] = Queue()

  private val useList = new HashMap[Term, Queue[PredicateApplication]] {
    override def default(k: Term) = {
      val v = Queue[PredicateApplication]()
      this += (k -> v)
      v
    }
  }

  val lookup: Map[(Term, Term), Option[PredicateApplication]] = Map().withDefaultValue(None)

  private val classList: Map[Term, Queue[Term]] = Map() ++ elems.map(el => (el, Queue(el)))

  def merge(eq: PredicateApplication) {
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

  private def reverseEdges(from: ProofStructureNode) {
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
    // reset makes explanations complete, but is it necessary?
    //println("Explaining why "+ c1 +" = "+ c2)
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
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

