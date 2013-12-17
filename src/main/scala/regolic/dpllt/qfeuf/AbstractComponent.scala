package regolic
package dpllt
package qfeuf

import scala.reflect._

trait AbstractComponent extends TheoryComponent {

  val literalClassTag: ClassTag[Literal] = classTag[PropositionalLiteral]

  type Literal = Lit
  type LiteralRepr = FastCongruenceClosure.InputEquation
  case class Lit(eq: FastCongruenceClosure.InputEquation, 
                 val id: Int, 
                 pol: Boolean, 
                 pred: PredicateApplication) extends AbstractLiteral {
    val polInt = if(pol) 1 else 0

    def pos = Lit(eq, id, true, pred)
    def neg = Lit(eq, id, if(pol) false else true, pred)

    override def toString: String = eq match {
      case Left((a, b)) if pol => "c_" + a + " = c_" + b
      case Left((a, b)) => "c_" + a + " != c_" + b
      case Right((a, b, c)) if pol => "f_" + a + "(c_" + b + ") = c_" + c
      case Right((a, b, c)) => "f_" + a + "(c_" + b + ") != c_" + c
    }
  }

  override def makeLiteral(id: Int, pol: Boolean, repr: LiteralRepr) = Lit(repr, id, pol, null)

}
