package regolic.sat

case class RefInputInference(id: Int, clause: Array[Literal]) extends Inference
case class RefResolutionInference(id: Int, clause: Array[Literal], leftPremiseRef: Int, rightPremiseRef: Int) extends Inference


class Proof(contradiction: Inference) {

  import scala.collection.mutable.ArrayBuffer
  import scala.collection.mutable.HashMap
  import scala.collection.mutable.Queue

  val inferences: Array[Inference] = {

    var inf2index: HashMap[Inference, Int] = new HashMap()
    var buffer: ArrayBuffer[Inference] = new ArrayBuffer()
    var i = 0
    var queue: Queue[Inference] = new Queue()
    queue.enqueue(contradiction)

    while(!queue.isEmpty) {
      val current = queue.dequeue

      if(!inf2index.contains(current)) {
        current match {
          case InputInference(cl) =>
            val newInf = RefInputInference(i, cl)
            inf2index(current) = i
            i += 1
            buffer.append(newInf)
          case ResolutionInference(cl, left, right) =>
            (inf2index.get(left), inf2index.get(right)) match {
              case (None, None) =>
                queue.enqueue(left)
                queue.enqueue(right)
                queue.enqueue(current)
              case (None, _) => 
                queue.enqueue(left)
                queue.enqueue(current)
              case (_, None) => 
                queue.enqueue(right)
                queue.enqueue(current)
              case (Some(il), Some(ir)) =>
                val newInf = RefResolutionInference(i, cl, il, ir)
                inf2index(current) = i
                i += 1
                buffer.append(newInf)
            }
          case _ => sys.error("unexpected")
        }
      }
    }

    buffer.toArray
  }

  override def toString: String = {
    def printClause(cl: Array[Literal]) = cl.mkString(", ")

    inferences.map{
      case RefInputInference(i, cl) => i + " - " + printClause(cl) + " - INPUT"
      case RefResolutionInference(i, cl, li, ri) => i + " - " + printClause(cl) + " - RES " + li + ", " + ri
    }.mkString("\n")

  }

}

object ProofChecker {

  def apply(proof: Proof): Boolean = {

    //println("checking proof:\n" + proof)

    var i = 0
    var isValid = true

    //make sure that every resolution step is valid
    while(i < proof.inferences.size && isValid) {
      proof.inferences(i) match {
        case RefInputInference(id, cl) => //input clause is valid
        case RefResolutionInference(id, cl, idLeft, idRight) => {
          if(idLeft < 0 || idLeft >= i || idRight < 0 || idRight >= i) //only refer to previous inferences
            isValid = false
          else {
            val inferenceLeft = proof.inferences(idLeft)
            val inferenceRight = proof.inferences(idRight)
            if(!isResolvent(cl, inferenceLeft.clause, inferenceRight.clause))
              isValid = false
          }
        }
      }
      i += 1
    }

    //verify that the final rule is the empty clause
    isValid && proof.inferences.last.clause.isEmpty
  }

  def isResolvent(resolvent: Array[Literal], left: Array[Literal], right: Array[Literal]): Boolean = {
    //println("Is resolvent:\n" + 
    //          left.mkString(", ") + "     " + right.mkString(", ") + "\n" +
    //          "======================\n" +
    //          resolvent.mkString(", "))
    left.exists(l1 => right.exists(l2 =>
      l1.id == l2.id && l1.polarity != l2.polarity && 
      resolvent.toSet == (left.filterNot(_ == l1).toSet ++ right.filterNot(_ == l2).toSet)
    ))
  }

}
