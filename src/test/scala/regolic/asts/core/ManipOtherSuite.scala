package regolic.asts.core

import org.scalatest.FunSuite

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._

import TestValues._

class ManipOtherSuite extends FunSuite {

  def isVar(t: Term) = t match {
    case Variable(_, _) => true
    case _ => false
  }
  def isCnst(t: Term) = t match {
    case FunctionApplication(_, List()) => true
    case _ => false
  }
  def fFalse(f: Formula) = false
  def tFalse(t: Term) = false


  test("findAndMap: identity of trivial terms") {
    assert(s2t("x") === findAndMap(s2t("x"), fFalse _, isVar _, fid _, tid _))
    assert(s2t("n") === findAndMap(s2t("n"), fFalse _, isCnst _, fid _, tid _))
    assert(s2t("fx") === findAndMap(s2t("fx"), fFalse _, isVar _, fid _, tid _))
    assert(s2t("hynz") === findAndMap(s2t("hynz"), fFalse _, isVar _, fid _, tid _))
    assert(s2t("gyn") != findAndMap(s2t("gxn"), fFalse _, isVar _, fid _, tid _))
    assert(s2t("Gxm") != findAndMap(s2t("gxm"), fFalse _, isCnst _, fid _, tid _))
  }

  test("findAndMap: identity of trivial formulas") {
    assert(s2f("qxy") === findAndMap(s2f("qxy"), fFalse _, isVar _, fid _, tid _))
    assert(s2f("pn") === findAndMap(s2f("pn"), fFalse _, isCnst _, fid _, tid _))
  }

//  def count(pf: (Formula) => Boolean, pt: (Term) => Boolean, t: Term): Int = fold(0, (a: Int, f: Formula) => if(pf(f)) a + 1 else a, (a: Int, t: Term) => if(pt(t)) a + 1 else a, t)
//  def count(pf: (Formula) => Boolean, pt: (Term) => Boolean, f: Formula): Int = fold(0, (a: Int, f: Formula) => if(pf(f)) a + 1 else a, (a: Int, t: Term) => if(pt(t)) a + 1 else a, f)
//  def vars(f: Formula): List[Variable] = fold(
//  def vars(t: Term): List[Variable] = fold(
//  def substitute(m: Map[Variable, Term], t: Term): Term = mapPostorder(f => f, t => t match {
//  def substitute(m: Map[Variable, Term], f: Formula): Formula = mapPostorder(f => f, t => t match {
//  def substitute(oldVar: Variable, newT: Term, t: Term): Term = substitute(Map(oldVar -> newT), t)
//  def substitute(oldVar: Variable, newT: Term, f: Formula): Formula = substitute(Map(oldVar -> newT), f)
//  def contains(t: Term, contained: Term): Boolean = fold(false,
//  def contains(f: Formula, contained: Term): Boolean = fold(false,

//  def foreachPreorder(ff: (Formula) => Unit, ft: (Term) => Unit, t: Term): Unit = foldPreorder((), (_: Unit, f: Formula) => ff(f), (_: Unit, t: Term) => ft(t), t)
//  def foreachPreorder(ff: (Formula) => Unit, ft: (Term) => Unit, f: Formula): Unit = foldPreorder((), (_: Unit, f: Formula) => ff(f), (_: Unit, t: Term) => ft(t), f)
//  def foreachPostorder(ff: (Formula) => Unit, ft: (Term) => Unit, t: Term): Unit = foldPostorder((), (_: Unit, f: Formula) => ff(f), (_: Unit, t: Term) => ft(t), t)
//  def foreachPostorder(ff: (Formula) => Unit, ft: (Term) => Unit, f: Formula): Unit = foldPostorder((), (_: Unit, f: Formula) => ff(f), (_: Unit, t: Term) => ft(t), f)
//  def exists(pf: (Formula) => Boolean, pt: (Term) => Boolean, t: Term): Boolean = fold(false, (b: Boolean, f: Formula) => b || pf(f) , (b: Boolean, t: Term) => (b || pt(t)), t)
//  def exists(pf: (Formula) => Boolean, pt: (Term) => Boolean, f: Formula): Boolean = fold(false, (b: Boolean, f: Formula) => b || pf(f) , (b: Boolean, t: Term) => (b || pt(t)), f)
//  def forall(pf: (Formula) => Boolean, pt: (Term) => Boolean, t: Term): Boolean = fold(true, (b: Boolean, f: Formula) => b && pf(f), (b: Boolean,t: Term) => (b && pt(t)), t)
//  def forall(pf: (Formula) => Boolean, pt: (Term) => Boolean, f: Formula): Boolean = fold(true, (b: Boolean, f: Formula) => b && pf(f), (b: Boolean,t: Term) => (b && pt(t)), f)
}
