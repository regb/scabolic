package regolic.smt.qfeuf

import regolic.smt.Solver
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.asts.theories.int.Trees.IntSort

import scala.collection.mutable.Queue
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.Set
import scala.collection.mutable.ArrayBuffer


class ProofStructureNode(val label: Term) {
  var parent: ProofStructureNode = null

  def hasParent = parent != null

  override def toString = {
    val to = if(hasParent) " [=> "+ parent.label +"]" else ""
    label + to
  }
}

class CongruenceClosure extends Solver {
//class CongruenceClosure(val eqs: List[Equation]) {
  // TODO change Maps to Arrays where the Term.id is the index
  // TODO collect EqClass stuff in separate object 

  val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  private var elems: Set[Term] = null

  var node: Map[Term,ProofStructureNode] = null

  private var repr: Map[Term,Term] = null
    
  private val pending: Queue[Any] = Queue()

  private val useList = new HashMap[Term, Queue[Equation]] {
    override def default(k: Term) = {
      val v = Queue[Equation]()
      this += (k -> v)
      v
    }
  }

  private val lookup: Map[(Term, Term), Option[Equation]] = Map().withDefaultValue(None)

  private var classList: Map[Term, Queue[Term]] = null

  // TODO maybe able to refactor this using ProofStructureNode
  private val labels: Map[Term,Any] = Map()

  def init(eqs: List[Equation]) {
    def extractVariables(t: Term) = t match {
      case FunctionApplication(_, List((c1: Variable), (c2: Variable))) => List(c1, c2)
      case Variable(_, _) => List(t)
      case _ => throw new Exception("Unexpected term "+ t)
    }
    elems = Set() ++ eqs.foldRight(List.empty[Term])((eq,l) =>
      extractVariables(eq._1) ::: extractVariables(eq._2) ::: l)
    node = Map() ++ elems.map{e => (e, new ProofStructureNode(e))}
    repr = Map() ++ elems.zip(elems)
    classList = Map() ++ elems.map(el => (el, Queue(el)))
    eqClass = Map() ++ node.values.zip(node.values)
  }

  def isSat(f: Formula): Option[scala.collection.immutable.Map[FunctionSymbol, Term]] = {
    val And(fs) = f
    val eqs = fs.map{x => x match {
      case Equals(t1, t2) => (t1, t2)
      case _ => throw new Exception("Formula "+ x +" is not an equality")
    }}
    init(eqs)
    Flattener(Currifier(eqs)).foreach(merge)

    fs.foreach{
      case Not(Equals((t1: Variable), (t2: Variable))) if areCongruent(t1, t2) => explain(t1,t2)
      case _ => ()
    }

    None
  }

  def merge(eq: Equation) {
    eq match {
      case (a: Variable, b: Variable) => {
        pending.enqueue(eq)
        propagate()
      }
      case (FunctionApplication(_, List(a1, a2)), a)  => {
        lookup(repr(a1),repr(a2)) match {
          case Some(f: Equation) => {
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

  private def propagate() {
    while(pending.nonEmpty) {
      val e = pending.dequeue()
      
      val p = e match {
        case (a: Variable, b: Variable) => (a,b)
        case ((_, a: Variable), (_, b: Variable)) => (a,b)
      }
      val (a, b) = if(classList(repr(p._1)).size > classList(repr(p._2)).size) p.swap else p

      if(repr(a) != repr(b)) {
        val oldreprA = repr(a)
        insertEdge(a, b)
        labels(a) = e

        while(classList(oldreprA).nonEmpty) {
          val c = classList(oldreprA).dequeue()
          repr(c) = repr(b)
          classList(repr(b)).enqueue(c)
        }

        while(useList(oldreprA).nonEmpty) {
          val f1 = useList(oldreprA).dequeue()
          val (FunctionApplication(_, List(c1, c2)),c) = f1

          lookup(repr(c1), repr(c2)) match {
            case Some(f2@(FunctionApplication(_, List(d1, d2)), d)) => {
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
          case Some((_, a)) if (u1.isInstanceOf[Variable] &&
            u2.isInstanceOf[Variable]) => repr(a)
          case _ => FunctionApplication(applyFun, List(u1.asInstanceOf[Variable],
            u2.asInstanceOf[Variable]))
        }
      }
    }
  }

  private def areCongruent(s: Term, t: Term): Boolean = {
    normalize(s) == normalize(t)
  }

  private val pendingProofs: Queue[(Term, Term)] = Queue()
  val highestNode: Map[ProofStructureNode, ProofStructureNode] = Map()
  private var eqClass: Map[ProofStructureNode,ProofStructureNode] = null

  private def insertEdge(e: Variable, ePrime: Variable) = {
    reverseEdges(node(e))
    node(e).parent = node(ePrime)
  }
  
  private def findEqClass(x: ProofStructureNode): ProofStructureNode = {
    if(eqClass(x) == x)
      x
    else
      findEqClass(eqClass(x))
  }

  // TODO lazy, efficient?
  private def computeHighestNode(c: ProofStructureNode): ProofStructureNode = {
    @annotation.tailrec
    def nestedComputeHighestNode(x: ProofStructureNode): ProofStructureNode = {
      if(highestNode.contains(x))
        highestNode(x)
      else {
        if(!x.hasParent || findEqClass(x.parent) != findEqClass(c)) 
          x
        else
          nestedComputeHighestNode(x.parent)
      }
    }
    val highest = nestedComputeHighestNode(c)
    highestNode(c) = highest
    highest
  }

  def nearestCommonAncestor(a: Term, b: Term): Option[ProofStructureNode] = {
    var i = node(a)
    var j = node(b)
    var m = 0
    // TODO add visited field to node, and check if visited fields are equal
    // at the pointers
    val visited = Map[ProofStructureNode, Boolean]().withDefaultValue(false)
    while(true) {
      if(visited(i) == true) 
        return Some(i)
      if(visited(j) == true) 
        return Some(j)

      // TODO see if it makes sense to optimize counting mechanism (m+=2 if
      // only one pointer running
      if(m % 2 == 0 && i.hasParent) {
        i = i.parent
        visited(i) = true
      } else if(m % 2 == 1 && j.hasParent) {
        j = j.parent
        visited(j) = true
      } else if(!i.hasParent && !j.hasParent) {
        return None
      }
      m += 1
    }

    throw new Exception("Unreachable code")
  }

  // TODO return explanation instead of instant print
  def explain(c1: Variable, c2: Variable) {
    pendingProofs.enqueue((c1, c2))
    while(pendingProofs.nonEmpty) {
      val (a, b) = pendingProofs.dequeue()
      val c = computeHighestNode(findEqClass(
        nearestCommonAncestor(a, b) match {
          case Some(x) => x
          case None => throw new Exception("No common ancestor "+ (a,b))
        }
      ))
      explainAlongPath(node(a), c)
      explainAlongPath(node(b), c)
    }
  }

  private def explainAlongPath(aL: ProofStructureNode, c: ProofStructureNode) {
    var a = computeHighestNode(aL)

    println("Explaining "+ (aL, c))
    while(a.label != c.label) {
      val b = a.parent
      labels(a.label) match {
        case (a: Variable, b: Variable) => println((a, b))
        case ((fa@FunctionApplication(_, List(a1, a2)), a: Variable),
          (fb@FunctionApplication(_, List(b1, b2)), b: Variable)) => {
          println((fa, a) +", "+ (fb, b))
          // TODO sufficient? nca call for Variable not in proof tree?
          if(a1 != b1)
            pendingProofs.enqueue((a1, b1))
          if(a2 != b2)
            pendingProofs.enqueue((a2, b2))
        }
      }
      // UNION
      eqClass(findEqClass(a)) = findEqClass(b)
      highestNode(a) = computeHighestNode(b)

      a = computeHighestNode(b)
    }
  }

}

object CongruenceClosure {
  def main(args: Array[String]) {
    val a = freshVariable("a", IntSort())
    val b = freshVariable("b", IntSort())
    val c = freshVariable("c", IntSort())
    val d = freshVariable("d", IntSort())
    val e = freshVariable("e", IntSort())
    val f = freshFunctionSymbol("f", List(IntSort(), IntSort()), IntSort())
    val g = freshVariable("g", IntSort())
    val h = freshVariable("h", IntSort())
    val eqs = List((FunctionApplication(f, List(g,h)), d), (c, d),
      (FunctionApplication(f, List(g,d)), a), (e, c), (e, b), (b, h))
    val cg = new CongruenceClosure()
    cg.init(eqs)
    eqs.foreach(cg.merge)
    println("proof structure")
    cg.node.values.foreach(println)
    cg.explain(a,b)
    println("\nhighestNode: "+ cg.highestNode.mkString(", "))

    val c1 = freshVariable("fresh", IntSort())
    val c2 = freshVariable("fresh", IntSort())
    val c3 = freshVariable("fresh", IntSort())
    val c4 = freshVariable("fresh", IntSort())
    val c5 = freshVariable("fresh", IntSort())
    val c6 = freshVariable("fresh", IntSort())
    val c7 = freshVariable("fresh", IntSort())
    val c8 = freshVariable("fresh", IntSort())
    val c9 = freshVariable("fresh", IntSort())
    val c10 = freshVariable("fresh", IntSort())
    val c11 = freshVariable("fresh", IntSort())
    val c12 = freshVariable("fresh", IntSort())
    val c13 = freshVariable("fresh", IntSort())
    val c14 = freshVariable("fresh", IntSort())
    val eqs2 = List((c1, c8), (c7, c2), (c3, c13), (c7, c1), (c6, c7), (c9,
      c5), (c9, c3), (c14, c11), (c10, c4), (c12, c9), (c4, c11), (c10, c7))
    val cg2 = new CongruenceClosure
    cg2.init(eqs2)
    eqs2.foreach(cg2.merge)
    println("nca: "+ cg2.nearestCommonAncestor(c8, c8))

    val t1 = freshVariable("t", IntSort())
    val t2 = freshVariable("t", IntSort())
    val t3 = freshVariable("t", IntSort())
    val t4 = freshVariable("t", IntSort())
    // TODO reverse edges test

    val gFun = freshFunctionSymbol("g", List(IntSort(), IntSort(), IntSort()), IntSort())
    val hFun = freshFunctionSymbol("h", List(IntSort(), IntSort()), IntSort())
    val eFun = freshFunctionSymbol("e", List(IntSort()), IntSort())
    val fFun = freshFunctionSymbol("f", List(IntSort()), IntSort())
    val toCurry = FunctionApplication(gFun, List(a, FunctionApplication(hFun,
      List(b, FunctionApplication(eFun, List(h)))), c))
    val iFun = freshFunctionSymbol("i", List(IntSort(), IntSort()), IntSort())
    val toCurry2 = FunctionApplication(iFun, List(d, e))
    println("curried: "+ Currifier(List((toCurry, toCurry2))))

    println("flatten: "+ Flattener(Currifier(List((toCurry, toCurry2)))))

    println("flatten: "+ Flattener(Currifier(List((FunctionApplication(fFun, List(a)), b)))))
  }

}
