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
  //private var diseq = Map[Term, collection.mutable.Set[Formula]]()
  private var diseq = new HashMap[(Int, Int), HashMap[Term, collection.mutable.Set[Formula]]] {
    override def default(k: Pair[Int, Int]) = {
      val v = new HashMap[Term, collection.mutable.Set[Formula]] {
        override def default(k: Term) = {
          val v = collection.mutable.Set[Formula]()
          this += (k -> v)
          v
        }
      }
      this += (k -> v)
      v
    }
  }
  //private var diseq = new HashMap[Term, collection.mutable.Set[Formula]] {
    //override def default(k: Term) = {
      //val v = collection.mutable.Set[Formula]()
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
    for(l <- ls) {
      println("l: "+ l)
      l match {
        case Equals(t1, t2) => {
          elems ++= extractVariables(t1)
          elems ++= extractVariables(t2)
          l match {
            case Equals((c1: Variable), (c2: Variable)) => {
              posLitList(c1) += l
              posLitList(c2) += l
            }
            case _ => ()
          }
        }
        case Not(Equals((c1: Variable), (c2: Variable))) => {
          negLitList(c1) += l
          negLitList(c2) += l
        }
        case _ => ()
      }
    }
    elems.foreach(e => {
        useList(e) = Queue[Formula]()
        //diseq(e) = collection.mutable.Set[Formula]()
        repr(e) = e
        classList(e) = Queue(e)
        node(e) = new ProofStructureNode(e, null)
      })
    repr = Map[Term,Term]() ++ elems.map(e => (e, e))
    classList = Map[Term, Queue[Term]]() ++ elems.map(el => (el, Queue(el)))
    node = Map[Term, ProofStructureNode]() ++ elems.map{e => (e, new ProofStructureNode(e, null))}
  }

  private val elems = collection.mutable.Set[Term]()

  /*
   * Example: 
   * a -> b -> c -> d
   * insert b -> e
   * a -> b <- c <- d
   *      '-> e
   * undo b -> e
   */
  def undoMerge(l: Formula) {
    while(!undoStack(l).isEmpty) {
      val (from, reversedTo) = undoStack(l).pop
      from.parent = null // remove edge b -> e
      reverseEdges(reversedTo) // reverse b <- c <- d
    }

    while(!reprChangeStack(l).isEmpty) {
      val change = reprChangeStack(l).pop
      repr(change.elem) = change.oldRepr
      classList(change.newRepr).dequeueFirst(_ == change.elem)
      classList(change.oldRepr).enqueue(change.elem)
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
    println("in tSolver backtrack")
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        undoMerge(iStack.pop)
      }}

      val s = iStack.top
    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
    println("t-backtracking done")
  }

  def explain(l: Formula): Set[Formula] = {
    l match{
      case Equals((e1: Variable), (d1: Variable)) => {
        explain(e1, d1)
      }
      case Not(Equals((d1: Variable), (e1: Variable))) => {
        val cause = negTable(l)
        val Not(Equals((d2: Variable), (e2: Variable))) = cause
        (explain(d1, d2) union explain(e1, e2)) + cause
      }
      case _ => throw new Exception("explain shouldn't be called on equalities containing functions")
    }
  }

  var node = Map[Term, ProofStructureNode]()

  private var repr = Map[Term, Term]()
    
  private val pending: Queue[Any] = Queue()

  private var useList = Map[Term, Queue[Formula]]()
  //private var useList = new HashMap[Term, Queue[Formula]] {
    //override def default(k: Term) = { // TODO initialize everything upfront
      //val v = Queue[Formula]()
      //this += (k -> v)
      //v
    //}
  //}

  //var lookup: Map[(Int, Int), Map[(Term, Term), Option[Formula]]] = Map().withDefaultValue(None)
  var lookup = new HashMap[(Int, Int), Map[(Term, Term), Option[Formula]]] {
    override def default(k: Pair[Int, Int]) = {
      val v = Map[(Term, Term), Option[Formula]]().withDefaultValue(None)
      this += (k -> v)
      v
    }
  }

  private var classList = Map[Term, Queue[Term]]()

  val iStack = new Stack[Formula]


  private val reprChangeStack = new HashMap[Formula, Stack[ReprChange]] {
    override def default(k: Formula) = {
      val v = Stack[ReprChange]()
      this += (k -> v)
      v
    }
  }
 
  class ReprChange(val elem: Term, val oldRepr: Term, val newRepr: Term)

  var negTable = Map[Formula, Formula]()

  var trigger: Formula = null

  var ctr = -1
  def setTrue(l: Formula): Option[Set[Formula]] = {
    ctr += 1
    trigger = l
    val retVal = l match {
      case eq@Equals(t1, t2) => {
        if(diseq((iStack.size, ctr)).values.exists(_ == Not(l))) { // inconsistent 
          None
        } else {
          val tConsequence = merge(eq)

          // TODO how slow is cloning?
          //Some(tConsequence)
          Some(Set.empty[Formula])
        }
      }
      case Not(Equals(t1, t2)) => {
        if(areCongruent(t1, t2)) { // inconsistent
          None
        } else {
          diseq((iStack.size, ctr))(t1) += l
          diseq((iStack.size, ctr))(t2) += l
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
          negTable ++= tConsequence.map(ineq => (ineq, l))
          //Some(tConsequence.toSet)
          Some(Set.empty[Formula])
        }
      }
      case _ => throw new Exception("Unsupported formula")
    }
    iStack.push(l)
    retVal
  }

  def merge(eq: Formula): Set[Formula] = {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pending.enqueue(eq)
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        lookup((iStack.size, ctr))(repr(a1),repr(a2)) match {
          case Some(eq2@Equals(Apply(_, _), _)) => {
            pending.enqueue((eq, eq2))
            propagate()
          }
          case _ => {
            lookup((iStack.size, ctr))((repr(a1), repr(a2))) = Some(eq)
            useList(repr(a1)).enqueue(eq)
            useList(repr(a2)).enqueue(eq)
            Set.empty[Formula] // no new unions, no T-consequences
          }
        }
      }
    }
  }
  
  private def propagate(): Set[Formula] = {
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

      // merge classes of a and b
      if(repr(a) != repr(b)) {
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
              if(diseq((iStack.size, ctr))(repr(t1)).contains(Not(Equals(repr(t1), repr(t2))))) {
                negTable(ineq) = Not(Equals(repr(t1), repr(t2)))
                true
              } else if(diseq((iStack.size, ctr))(repr(t1)).contains(Not(Equals(repr(t2), repr(t1))))) {
                negTable(ineq) = Not(Equals(repr(t2), repr(t1)))
                true
              } else {
                false
              }
            }
          }}

          reprChangeStack(trigger).push(new ReprChange(c, repr(c), repr(b)))
          repr(c) = repr(b)
          classList(repr(b)).enqueue(c)
        }

        while(useList(oldreprA).nonEmpty) {
          val f1 = useList(oldreprA).dequeue()
          val Equals(Apply(c1, c2),c) = f1

          lookup((iStack.size, ctr))(repr(c1), repr(c2)) match {
            case Some(f2@Equals(Apply(d1, d2), d)) => {
              pending.enqueue((f1, f2))
            }
            case _ => {
              lookup((iStack.size, ctr))((repr(c1), repr(c2))) = Some(f1)

              useList(repr(b)).enqueue(f1)
            }
          }
        }
      }
      assert(repr(a) == repr(b))
    }
    tConsequence.toSet
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => repr.getOrElse(c, c)
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        lookup((iStack.size, ctr))(u1, u2) match {
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

  private val undoStack = new HashMap[Formula, Stack[Pair[ProofStructureNode, ProofStructureNode]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[ProofStructureNode, ProofStructureNode]]()
      this += (k -> v)
      v
    }
  }
  
  private def insertEdge(a: Variable, b: Variable, label: Any) = {
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    val from = node(a)
    val reversedTo = reverseEdges(from)
    from.parent = node(b)
    from.edgeLabel = label
    //println(node.values.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    //println("inserted "+ a +" -> "+ b +" repr a: "+ repr(a) +", repr b: "+ repr(b))
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

