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

  class CongruenceClosure(val eqs: List[Equation]) {

    private def extractConstants(t: Term) = t match {
      case Function(_, args) => List(args._1, args._2)
      case c@Constant(_) => List(c)
    }
    val elems: Set[Constant] = Set() ++ eqs.foldRight(List.empty[Constant])((eq,l) =>
      extractConstants(eq._1) ::: extractConstants(eq._2) ::: l)

    val edges: Map[Constant,Constant] = Map()
    val labels: Map[Constant,Any] = Map()

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

    def computePath(e: Constant): List[(Constant, Constant)] = {
      def innerComputePath(e: Constant, acc: List[(Constant, Constant)]): List[(Constant, Constant)] = {
        if(!edges.contains(e))
          acc
        else {
          val edge = (e, edges(e))
          innerComputePath(edges(e), edge :: acc)
        }
      }
      val retVal = innerComputePath(e, Nil)
      retVal
    }

    def insertEdge(e: Constant, ePrime: Constant) = {
      computePath(e).foreach(edge => {
          edges(edge._2) = edge._1
          edges -= edge._1
        })
      edges(e) = ePrime
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
          //println("insertEdge: "+ (a, b) +" sizes: "+ (classList(repr(a)).size,
            //classList(repr(b)).size))
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
    val highestNode: Map[Constant, Constant] = Map()
    val eqClass: Map[Constant,Constant] = Map() ++ elems.zip(elems)

    def findEqClass(x: Constant): Constant = {
      if(eqClass(x) == x)
        x
      else
        findEqClass(eqClass(x))
    }

    // TODO lazy, efficient?
    def computeHighestNode(c: Constant): Constant = {
      println("c: "+ c)
      def computeHighestNodeInner(x: Constant): Constant = {
        if(highestNode.contains(x))
          highestNode(x)
        else {
          if(!edges.contains(x) || eqClass(edges(x)) != eqClass(c)) 
            x
          else
            computeHighestNodeInner(edges(x))
        }
      }
      val highest = computeHighestNodeInner(c)
      highestNode(c) = highest
      println("highest: "+ highest)
      highest
    }

    def nearestCommonAncestor(a: Constant, b: Constant): Option[Constant] = {
      var i = a
      var j = b
      var m = 0
      val visited = Map[Constant, Boolean]().withDefaultValue(false)
      while(true) {
        if(visited(i) == true) 
          return Some(i)
        if(visited(j) == true) 
          return Some(j)

        // TODO see if it makes sense to optimize counting mechanism (m+=2 if
        // only one pointer running
        if(m % 2 == 0 && edges.contains(i)) {
          i = edges(i)
          visited(i) = true
        } else if(m % 2 == 1 && edges.contains(j)) {
          j = edges(j)
          visited(j) = true
        } else if(!edges.contains(i) && !edges.contains(j)) {
          return None
        }
        m += 1
      }

      throw new Exception("Unreachable code")
    }

    def explain(c1: Constant, c2: Constant) {
      pendingProofs.enqueue((c1, c2))
      while(pendingProofs.nonEmpty) {
        val (a, b) = pendingProofs.dequeue()
        //println("highestNode:\n"+highestNode.mkString("\n"))
        val c = computeHighestNode(findEqClass(
          nearestCommonAncestor(a, b) match {
            case Some(x) => {println("nearestCommonAncestor("+a+","+b+"): "+ x); x}
            case None => throw new Exception("No common ancestor "+ (a,b))
          }
        ))
        explainAlongPath(a, c)
        explainAlongPath(b, c)
      }
    }

    def explainAlongPath(aL: Constant, c: Constant) {
      var a = computeHighestNode(findEqClass(aL))

      println("Explaining "+ (aL, c))
      while(a != c) {
        val b = edges(a)
        labels(a) match {
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
        eqClass(a) = findEqClass(b)
        highestNode(a) = computeHighestNode(findEqClass(b)) //TODO just b should be enough since b is in same eqClass as findEqClass(b)

        a = computeHighestNode(findEqClass(b))
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

      println("\nedges: "+ cg.edges.mkString(", "))
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
      println("\nedges: "+ cg2.edges.mkString(", "))
      println("nca: "+ cg2.nearestCommonAncestor(c8, c8))

      val t1 = Constant("t1")
      val t2 = Constant("t2")
      val t3 = Constant("t3")
      val t4 = Constant("t4")
      cg2.edges ++= Set((t1,t2), (t2, t3), (t3, t4))
      println("path "+ cg2.computePath(t1))
    }

  }
}
