package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.theories.int.Trees.IntSort

package object qfeuf {

  // 2-ary apply symbol
  val applyFun = freshFunctionSymbol("apply", List(IntSort(), IntSort()), IntSort())
}

