package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.theories.int.Trees.IntSort

package object qfeuf {

  // 2-ary apply symbol
  val applyFun = freshFunctionSymbol("apply", List(IntSort(), IntSort()), IntSort())

  // Would be nicer if this were Pair[Term, Variable] (or Constant instead of
  // Variable)
  type Equation = Pair[Term, Term]
}

