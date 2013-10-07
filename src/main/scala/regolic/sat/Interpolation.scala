package regolic.sat

object Interpolation {

  sealed trait Form
  case class And(fs: List[Form]) extends Form
  case class Or(fs: List[Form]) extends Form
  case class Lit(lit: Literal) extends Form
  case object True extends Form


  def apply(proof: Proof, leftFormulas: Set[Set[Literal]], rightFormulas: Set[Set[Literal]]): Form = {
    require(proof.isFinalized)

    val inferences: Array[Inference] = proof.inferences

    val index  = new scala.collection.mutable.HashMap[Inference, Int]
    val p = new scala.collection.mutable.HashMap[Set[Literal], Form]

    val localVariables: Set[Int] = leftFormulas.flatMap(_.map(_.id)).diff(rightFormulas.flatMap(_.map(_.id)))
    val globalVariable: Set[Int] = leftFormulas.flatMap(_.map(_.id)).intersect(rightFormulas.flatMap(_.map(_.id)))


    def g(clause: Set[Literal]): Form = Or(clause.flatMap((lit: Literal) => 
      if(globalVariable.contains(lit.id)) List(Lit(lit)) else List()
    ).toList)
    def l(clause: Set[Literal]): Form = And(clause.flatMap((lit: Literal) => 
      if(localVariables.contains(lit.id)) List(Lit(lit)) else List()
    ).toList)

    inferences.zipWithIndex.foreach{
      case (inf@InputInference(clause), i) => {
        if(leftFormulas.contains(clause))
          p(clause) = g(clause)
        else
          p(clause) = True
      }
      case (inf@ResolutionInference(clause, left, right), i) => {
        val pivot = left.clause.find(lit => right.clause.exists(lit2 => lit.id == lit2.id && lit.polInt != lit2.polInt)).get.id
        if(localVariables.contains(pivot))
          p(clause) = Or(List(p(left.clause), p(right.clause)))
        else
          p(clause) = And(List(p(left.clause), p(right.clause)))
      }
    }

    p(Set())
  }

}
