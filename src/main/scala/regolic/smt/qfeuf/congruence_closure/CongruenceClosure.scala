import scala.collection.mutable.Queue
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.Set
import scala.collection.mutable.ArrayBuffer

package object congruenceclosure {
  abstract class Term(name: String)

  case class Function(name: String, args: Pair[Constant, Constant]) extends Term(name) 

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

    val useList: Map[Constant, Queue[Equation]] = Map().withDefaultValue(
      Queue[Equation]())

    val lookup: Map[(Term, Term), Option[Equation]] = Map().withDefaultValue(None)

    val classList: Map[Constant, Queue[Constant]] = Map() ++ elems.map(el =>
      (el, Queue(el)))

    println("elems:\n"+ elems.mkString("\n"))

    def merge(eq: Equation) {
      println("merging: "+ eq)
      eq match {
        case (s: Constant, t: Constant) => {
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
    
    private def propagate() {
      while(pending.nonEmpty) {
        val e = pending.dequeue()
        val (a,b) = e match {
          case (a: Constant, b: Constant) => (a,b)
          case ((_, a: Constant), (_, b: Constant)) => (a,b)
        }
        println("(a,b): "+ (a,b) +", (a',b'): "+ (repr(a), repr(b)))

        if(repr(a) != repr(b) && classList(repr(a)).size <= classList(repr(b)).size) {
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
                println("adding: "+ (f1, f2))
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

      println("\nrepr: "+ cg.repr.mkString(", "))
      println("\nedges: "+ cg.edges.mkString(", "))
    }

  }
}
