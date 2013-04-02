package regolic.sat

import org.scalatest.FunSuite

class ProofCheckerSuite extends FunSuite {

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)
  private val emptyClause = Set[Literal]()

  test("Basic Proof") {
    val cl1 = Set(na)
    val cl2 = Set(a, b)
    val cl3 = Set(a, nb)

    val cl4 = Set(b)
    val cl5 = Set(nb)

    val proof = new Proof(Set(cl1, cl2, cl3))
    proof.infer(cl1, cl2, cl4)
    proof.infer(cl1, cl3, cl5)
    proof.infer(cl4, cl5, emptyClause)
    println(proof.linearize(emptyClause).mkString("\n"))
    assert(ProofChecker(proof, emptyClause))
  }

}
