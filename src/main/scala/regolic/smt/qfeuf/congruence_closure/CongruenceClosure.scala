import scala.collection.mutable.Queue
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.Set
import scala.collection.mutable.ArrayBuffer

package object congruenceclosure {
  abstract class Term(name: String) {
    override def toString = name

    //implicit def toInt = this.id
  }

  case class Function(name: String, args: Pair[Constant, Constant]) extends Term(name) {
    override def toString = name +"("+ args._1 +","+ args._2 +")"
  }

  case class Constant(name: String) extends Term(name)

  type Equation = Pair[Term, Constant]
}

package congruenceclosure {

  object Currifier {

    def curry(t: Term): Function = {
      def makeF(terms: List[Term]): Function = {
        terms match {
          case x :: xs => Function("f", makeF(xs) :: curry(x))
          case x :: Nil => x
          case _ => throw new Exception("impossible case")
        }
      }

      if(t.isInstanceOf[Constant])
        t
      else {
        val Function(name, args) = t
        makeF((Constant(name) :: args).reverse)
      }
    }
  }

  class ProofStructureNode(val label: Constant) {
    var parent: ProofStructureNode = null

    def hasParent = parent != null

    override def toString = {
      val to = if(hasParent) " [=> "+ parent.label +"]" else ""
      label + to
    }
  }

  // TODO make stuff private
  class CongruenceClosure(val eqs: List[Equation]) {
    // TODO change Maps to Arrays where the Term.id is the index

    private def extractConstants(t: Term) = t match {
      case Function(_, args) => List(args._1, args._2)
      case c@Constant(_) => List(c)
    }
    val elems: Set[Constant] = Set() ++ eqs.foldRight(List.empty[Constant])((eq,l) =>
      extractConstants(eq._1) ::: extractConstants(eq._2) ::: l)

    val node: Map[Constant,ProofStructureNode] = Map() ++ elems.map{e => (e,
      new ProofStructureNode(e))}

    val repr: Map[Constant,Constant] = Map() ++ elems.zip(elems)
      
    val pending: Queue[Any] = Queue()

    val useList = new HashMap[Constant, Queue[Equation]] {
      override def default(k: Constant) = {
        val v = Queue[Equation]()
        this += (k -> v)
        v
      }
    }

    val lookup: Map[(Term, Term), Option[Equation]] = Map().withDefaultValue(None)

    val classList: Map[Constant, Queue[Constant]] = Map() ++ elems.map(el =>
      (el, Queue(el)))

    // TODO maybe able to refactor this using ProofStructureNode
    val labels: Map[Constant,Any] = Map()

    def merge(eq: Equation) {
      eq match {
        case (a: Constant, b: Constant) => {
          pending.enqueue(eq)
          propagate()
        }
        case (Function(_, (a1, a2)), a)  => {
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

    def reverseEdges(from: ProofStructureNode) {
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

    def insertEdge(e: Constant, ePrime: Constant) = {
      reverseEdges(node(e))
      node(e).parent = node(ePrime)
    }
    
    private def propagate() {
      while(pending.nonEmpty) {
        val e = pending.dequeue()
        
        val p = e match {
          case (a: Constant, b: Constant) => (a,b)
          case ((_, a: Constant), (_, b: Constant)) => (a,b)
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
            val (Function(_, (c1, c2)),c) = f1

            lookup(repr(c1), repr(c2)) match {
              case Some(f2@(Function(_, (d1, d2)), d)) => {
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
        case c@Constant(_) => repr(c)
        case Function(_, (t1, t2)) => {
          val u1 = normalize(t1)
          val u2 = normalize(t2)
          lookup(u1, u2) match {
            case Some((_, a)) if (u1.isInstanceOf[Constant] &&
              u2.isInstanceOf[Constant]) => repr(a)
            case _ => Function("f", (u1.asInstanceOf[Constant],
              u2.asInstanceOf[Constant]))
          }
        }
      }
    }

    def areCongruent(s: Term, t: Term): Boolean = {
      normalize(s) == normalize(t)
    }

    val pendingProofs: Queue[(Constant, Constant)] = Queue()
    val highestNode: Map[ProofStructureNode, ProofStructureNode] = Map()
    val eqClass: Map[ProofStructureNode,ProofStructureNode] = Map() ++ node.values.zip(node.values)

    def findEqClass(x: ProofStructureNode): ProofStructureNode = {
      if(eqClass(x) == x)
        x
      else
        findEqClass(eqClass(x))
    }

    // TODO lazy, efficient?
    def computeHighestNode(c: ProofStructureNode): ProofStructureNode = {
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

    def nearestCommonAncestor(a: Constant, b: Constant): Option[ProofStructureNode] = {
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
    def explain(c1: Constant, c2: Constant) {
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

    def explainAlongPath(aL: ProofStructureNode, c: ProofStructureNode) {
      var a = computeHighestNode(aL)

      println("Explaining "+ (aL, c))
      while(a.label != c.label) {
        val b = a.parent
        labels(a.label) match {
          case (a: Constant, b: Constant) => println((a, b))
          case ((fa@Function(_, (a1, a2)), a: Constant), (fb@Function(_, (b1,
            b2)), b: Constant)) => {
            println((fa, a) +", "+ (fb, b))
            // TODO sufficient? nca call for constant not in proof tree?
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
      val a = Constant("a")
      val b = Constant("b")
      val c = Constant("c")
      val d = Constant("d")
      val e = Constant("e")
      val g = Constant("g")
      val h = Constant("h")
      val eqs = List((Function("f", (g,h)), d), (c, d), (Function("f", (g,d)),
        a), (e, c), (e, b), (b, h))
      val cg = new CongruenceClosure(eqs)
      cg.eqs.foreach(cg.merge)
      println("proof structure")
      cg.node.values.foreach(println)
      cg.explain(a,b)
      println("\nhighestNode: "+ cg.highestNode.mkString(", "))

      val c1 = Constant("c1")
      val c2 = Constant("c2")
      val c3 = Constant("c3")
      val c4 = Constant("c4")
      val c5 = Constant("c5")
      val c6 = Constant("c6")
      val c7 = Constant("c7")
      val c8 = Constant("c8")
      val c9 = Constant("c9")
      val c10 = Constant("c10")
      val c11 = Constant("c11")
      val c12 = Constant("c12")
      val c13 = Constant("c13")
      val c14 = Constant("c14")
      val eqs2 = List((c1, c8), (c7, c2), (c3, c13), (c7, c1), (c6, c7), (c9,
        c5), (c9, c3), (c14, c11), (c10, c4), (c12, c9), (c4, c11), (c10, c7))
      val cg2 = new CongruenceClosure(eqs2)
      cg2.eqs.foreach(cg2.merge)
      println("nca: "+ cg2.nearestCommonAncestor(c8, c8))

      val t1 = Constant("t1")
      val t2 = Constant("t2")
      val t3 = Constant("t3")
      val t4 = Constant("t4")
      // TODO reverse edges test
    }

  }
}
