package regolic.asts.core

import Trees._
import Manip._
import org.scalatest.FunSuite

import TestValues._

class ManipFoldSuite extends FunSuite {

  def incifx(acc: Int, t: Term): Int = if(x == t) acc+1 else acc
  def fvoid[A](acc: A, f: Formula): A = acc
  def tvoid[A](acc: A, t: Term): A = acc

  test("foldPreorder: basic over terms") {
    assert(foldPreorder(x, 0)(fvoid, incifx) === 1)
    assert(foldPreorder(y, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(n, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(fx, 0)(fvoid, incifx) === 1)
    assert(foldPreorder(fy, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(fn, 0)(fvoid, incifx) === 0)
    assert(foldPreorder(gxn, 0)(fvoid, incifx) === 1)
    assert(foldPreorder(gxx, 0)(fvoid, incifx) === 2)
    assert(foldPreorder(gym, 0)(fvoid, incifx) === 0)
  }
  test("foldPreorder: basic over formulas") {
    assert(foldPreorder(s2f("px"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("qxn"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("qnx"), 0)(fvoid, incifx) === 1)
    assert(foldPreorder(s2f("py"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("pn"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("qyy"), 0)(fvoid, incifx) === 0)
    assert(foldPreorder(s2f("qnm"), 0)(fvoid, incifx) === 0)
  }
  test("foldPostorder: basic over terms") {
    assert(foldPostorder(x, 0)(fvoid, incifx) === 1)
    assert(foldPostorder(y, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(n, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(fx, 0)(fvoid, incifx) === 1)
    assert(foldPostorder(fy, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(fn, 0)(fvoid, incifx) === 0)
    assert(foldPostorder(gxn, 0)(fvoid, incifx) === 1)
    assert(foldPostorder(gxx, 0)(fvoid, incifx) === 2)
    assert(foldPostorder(gym, 0)(fvoid, incifx) === 0)
  }
  test("foldPostorder: basic over formulas") {
    assert(foldPostorder(s2f("px"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("qxn"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("qnx"), 0)(fvoid, incifx) === 1)
    assert(foldPostorder(s2f("py"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("pn"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("qyy"), 0)(fvoid, incifx) === 0)
    assert(foldPostorder(s2f("qnm"), 0)(fvoid, incifx) === 0)
  }

  test("foldPreorder: complex over terms") {
    assert(foldPreorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPreorder: complex over formula") {
    assert(foldPreorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPostorder: complex over terms") {
    assert(foldPostorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
  test("foldPostorder: complex over formula") {
    assert(foldPostorder(s2t("ipxiqxynxhxxgnx"), 0)(fvoid, incifx) === 6)
  }
}
