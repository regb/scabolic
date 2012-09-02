package regolic.sat

abstract class Inference {
  val clause: Array[Literal]
}

case class ResolutionInference(clause: Array[Literal], leftPremise: Inference, rightPremise: Inference) extends Inference
case class InputInference(clause: Array[Literal]) extends Inference
