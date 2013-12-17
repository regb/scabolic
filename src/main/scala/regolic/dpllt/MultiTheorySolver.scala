//package regolic
//package dpllt
//
//class MultiTheorySolver extends TheorySolver {
//
//  private val propositionalSolver = new PropositionalSolver
//  private val ufSolver = new smt.qfeuf.FastCongruenceClosure
//
//  private val iStack = new scala.collection.mutable.Stack[(TheorySolver, Literal)]
//
//  def initialize(ls: Set[Literal]): Unit = {
//    propositionalSolver.initialize(ls)
//    ufSolver.initialize(ls)
//  }
//
//  def isTrue(l: Literal): Boolean = {
//    if(l.isInstanceOf[smt.qfeuf.Literal])
//      ufSolver.isTrue(l)
//    else
//      propositionalSolver.isTrue(l)
//  }
//
//  def backtrack(n: Int): Unit = {
//    for(i <- 0 until n) {
//      val (solver, lit) = iStack.pop
//      solver.backtrack(1)
//    }
//  }
//
//  def setTrue(l: Literal): Set[Literal] = {
//    if(l.isInstanceOf[smt.qfeuf.Literal]) {
//      iStack.push((ufSolver, l))
//      ufSolver.setTrue(l)
//    } else {
//      iStack.push((propositionalSolver, l))
//      propositionalSolver.setTrue(l)
//    }
//  }
//
//  def explanation(l: Literal): Set[Literal] = {
//    assert(false)
//    Set()
//  }
//
//}
