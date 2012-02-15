package regolic.smt.logics.qflia

import Trees._

object Transformations {
/*
  def flatten(formula: Formula): Formula = formula.mapPostorder(flattenOne, flattenOne)
  def flattenOne(f: Formula): Formula = regolic.asts.fol.Transformations.flattenOne(f)

  def flatten(term: Term): Term = term.mapTermsPostorder(flattenOne)
  def flattenOne(t: Term): Term = t match {
    case Add(ts) => 
      Add(ts.foldLeft(Nil: List[Term])((a, t) => t match {
        case Add(ts2) => a ::: ts2
        case t2 => a ::: List(t2)
      }))
    case _ => t
  }

  def reduce(formula: Formula): Formula = fix(comp(reduceOne, (f: Formula) => flatten(f)), formula)

  def reduceOne(f: Formula): Formula = regolic.asts.fol.Transformations.reduceOne(f)

  def removeOneMax(term: Term): Term = term match {
    case Max(Nil) => error("Max of 0 term")
    case Max(t :: Nil) => t
    case Max(t :: ts) => ITE(And(ts.map(t2 => GreaterEqual(t, t2))), t, removeOneMax(Max(ts)))
    case _ => term
  }

  def removeMax(term: Term): Term = term.mapTerms(removeOneMax)

  def removeMax(formula: Formula): Formula = formula.mapTerms(removeOneMax)

  def undefinedFunApp(formula: Formula): Set[asts.fol.Trees.FunctionApplication] = {
    def isUndefined(term: asts.fol.Trees.FunctionApplication): Boolean = term match {
      case Add(_) | Sub(_,_) | Mul(_,_) | Number(_) => false
      case _ => true
    }
    formula.functionApplications.filter(isUndefined)
  }
  */

}
