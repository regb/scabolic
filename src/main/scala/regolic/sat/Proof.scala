package regolic.sat

import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.Queue

class Proof(inputs: Set[InputInference]) {


  private val literalsToInferences: HashMap[Set[Literal], Inference] = new HashMap()
  literalsToInferences ++= inputs.map(r => (r.clause, r))

  //this builds a resolution inference without any check
  //we assume that a separate proof checker has the duty to make sure
  //each inference is correct.
  //This code ensures that the inferences are already present in
  //the proof and make sure to reuse existing node as much as possible
  def infer(left: Set[Literal], right: Set[Literal], concl: Set[Literal]) {
    literalsToInferences.get(concl) match {
      case Some(_) =>
      case None =>
        val leftInf = literalsToInferences(left)
        val rightInf = literalsToInferences(right)
        val inf = new ResolutionInference(concl, leftInf, rightInf)
        literalsToInferences(concl) = inf
    }
  }

  def linearize(conclusion: Set[Literal]): Array[Inference] = {
    var buffer: List[Inference] = List()
    var inferencesAdded = new HashSet[Inference]
    var queue: Queue[Inference] = new Queue()
    queue.enqueue(literalsToInferences(conclusion))
    while(!queue.isEmpty) {
      val inf = queue.dequeue
      if(!inferencesAdded.contains(inf)) {
        buffer ::= inf
        inf match {
          case ResolutionInference(_, left, right) =>
            queue.enqueue(left)
            queue.enqueue(right)
          case InputInference(_) =>
        }
      }
    }
    buffer.toArray
  }

}

// vim: set ts=4 sw=4 et:
