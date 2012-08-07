package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._



trait Solver {

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]]
  def isSat(f: Formula): Option[Map[PredicateApplication, Boolean]] = {
    if(isConjunctiveNormalForm(f)) {
      val And(fs) = f
      isSat(fs)
    } else {
      val initialVars: Set[PredicateApplication] = propVars(f)
      val equisatFormulas = conjunctiveNormalFormEquisat(f)
      isSat(equisatFormulas) match {
        case None => None
        case Some(map) => Some(map.filter{ case (v, _) => initialVars.contains(v) })
      }
    }
  }

}
