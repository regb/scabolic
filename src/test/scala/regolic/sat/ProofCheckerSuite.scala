package regolic.sat

import org.scalatest.FunSuite

class ProofCheckerSuite extends FunSuite {

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)

  test("Basic Proof") {

    val cl1 = Array(na)
    val cl2 = Array(a, b)
    val cl3 = Array(a, nb)

    val cl4 = Array(b)
    val cl5 = Array(nb)

    val proof = ResolutionInference(Array(), 
                  ResolutionInference(cl4, 
                    InputInference(cl1),
                    InputInference(cl2)),
                  ResolutionInference(cl5,
                    InputInference(cl1),
                    InputInference(cl3))
                )

    assert(ProofChecker(new Proof(proof)))
  }

}
