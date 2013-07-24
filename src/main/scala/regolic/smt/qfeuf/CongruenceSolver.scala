package regolic.smt.qfeuf

import regolic.smt.Solver
import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._
import regolic.parsers.SmtLib2.Trees.QF_UF

import scala.collection.mutable.HashMap

object CongruenceSolver extends Solver {

  val logic = QF_UF

  def isSat(f: Formula): Option[Map[FunctionSymbol, Term]] = {

    val Or(ands) = disjunctiveNormalForm(f)

    var modelFound = false

    for(And(lits) <- ands if !modelFound) {
      isSat(lits) match {
        case Some(_) => modelFound = true
        case _ => 
      }
    }

    if(modelFound) Some(Map()) else None
  }

  def isSat(lits: List[Formula]): Option[Map[FunctionSymbol, Term]] = {
    val t2dag: HashMap[Term, Dag] = new HashMap

    //using mapPostorder (with side effect) to force the evaluation bottom up and the construction of the dags
    mapPostorder(And(lits), (f: Formula) => f, (t: Term) => {
      t2dag.get(t) match {
        case Some(dag) => t //nothing to do
        case None => {
          val args: List[Dag] = t match {
            case FunctionApplication(_, ts) => ts.map(t => t2dag(t))
            case Variable(_, _) => Nil
            case _ => sys.error("Unsupported term")
          }
          val dag = new Dag(t, args, null, Set())
          dag.find = dag //setting representative to itself
          //now setting the parents of all its children
          args.foreach(d => d.ccpar = d.ccpar ++ Set(dag))
          t2dag.put(t, dag)
          t
        }
      }
    })

    //merging of initial equalities
    lits.foreach{ 
      case Equals(t1, t2) => merge(t2dag(t1), t2dag(t2))
      case _ => ()
    }

    if(!lits.exists{ 
        case Not(Equals(t1, t2)) => t2dag(t1) === t2dag(t2)
        case _ => false }) {
      Some(Map())
    } else None
  }


  def isCongruent(d1: Dag, d2: Dag): Boolean = (d1.term, d2.term) match {
    case (FunctionApplication(s1, args1), FunctionApplication(s2, args2)) if s1 == s2 => d1.args.zip(d2.args).forall{ case (a1, a2) => a1 === a2 }
      //here we are supposed (according to the algorithm from Calculus of Computation, Bradley) 
      //to verify that both functions have the same numbers of arguments, but this has to be the case with our symbol representation
    case _ => false
  }

  def merge(d1: Dag, d2: Dag) {
    if(d1.findRepr() != d2.findRepr()) {
      val p1 = d1.parents()
      val p2 = d2.parents()
      d1.union(d2)
      for(t1 <- p1)
        for(t2 <- p2)
          if(t1.findRepr() != t2.findRepr() && isCongruent(t1, t2))
            merge(t1, t2)
    }
  }

}
