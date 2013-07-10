import scala.collection.mutable.Queue
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.Set
import scala.collection.mutable.ArrayBuffer

package object congruenceclosure {
  abstract class Term(name: String) {
    override def toString = name
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

    val edges: Map[(Term,Term), Any] = Map()

    val repr: Map[Constant,Constant] = Map() ++ elems.zip(elems)
      
    val pending: Queue[Any] = Queue()

    val useList: Map[Constant, Queue[Equation]] = Map().withDefaultValue(Queue())

    val lookup: Map[(Term, Term), Option[Equation]] = Map().withDefaultValue(None)

    val classList: Map[Constant, Queue[Constant]] = Map() ++ elems.map(el =>
      (el, Queue(el)))

    def initUseList(key: Constant) {
      if(!useList.contains(key))
        useList(key) = Queue()
    }
    def addToUseList(k: Constant, v: Equation) {
      if(!useList.contains(k))
        useList(k) = Queue()
      useList(k).enqueue(v)
    }

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

              addToUseList(repr(a1), eq)
              addToUseList(repr(a2), eq)
            }
          }
        }
      }
    }
    
    private def propagate() {
      while(pending.nonEmpty) {
        val e = pending.dequeue()
        
        val p = e match {
          case (a: Constant, b: Constant) => (a,b)
          case ((_, a: Constant), (_, b: Constant)) => (a,b)
        }
        val (a,b) = if(classList(repr(p._1)).size > classList(repr(p._2)).size) p.swap else p

        if(repr(a) != repr(b)) {
          val oldreprA = repr(a)
          edges((a,b)) = e

          while(classList(oldreprA).nonEmpty) {
            val c = classList(oldreprA).dequeue()
            repr(c) = repr(b)
            classList(repr(b)).enqueue(c)
          }

          while(useList(oldreprA).nonEmpty) {
            val f1 = useList(oldreprA).dequeue
            val (Function(_, (c1, c2)),c) = f1

            lookup(repr(c1), repr(c2)) match {
              case Some(f2@(Function(_, (d1, d2)), d)) => {
                pending.enqueue((f1, f2))
              }
              case _ => {
                lookup((repr(c1), repr(c2))) = Some(f1)

                addToUseList(repr(b), f1)
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

    def explain(): Option[Array[Equation]] = {
      None
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
    }

  }
}
