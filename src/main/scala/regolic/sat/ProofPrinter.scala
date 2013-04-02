package regolic.sat

import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer

object ProofPrinter {

  def toDot(inferences: Array[Inference]): String = {

    val infToIndex = new HashMap[Inference, Int]
    var i = 0

    while(i < inferences.size) {

    }

    var vertexLabels: Set[(String, String)] = Set()
    var vertexId = -1
    var point2vertex: Map[ProgramPoint, Int] = Map()
    //return id and label
    def getVertex(p: ProgramPoint): (String, String) = point2vertex.get(p) match {
      case Some(id) => ("v_" + id, ppPoint(p))
      case None => {
        vertexId += 1
        point2vertex += (p -> vertexId)
        val pair = ("v_" + vertexId, ppPoint(p))
        vertexLabels += pair
        pair
      }
    }

    def ppPoint(p: ProgramPoint): String = p match {
      case FunctionStart(fd) => fd.id.name
      case ExpressionPoint(Waypoint(i, e), _) => "WayPoint " + i
      case ExpressionPoint(e, _) => e.toString
    }
    def ppLabel(l: TransitionLabel): String = {
      val TransitionLabel(cond, assignments) = l
      cond.toString + ", " + assignments.map(p => p._1 + " -> " + p._2).mkString("\n")
    }

    val edges: List[(String, String, String)] = graph.flatMap(pair => {
      val (startPoint, edges) = pair
      val (startId, _) = getVertex(startPoint)
      edges.map(pair => {
        val (endPoint, label) = pair
        val (endId, _) = getVertex(endPoint)
        (startId, endId, ppLabel(label))
      }).toList
    }).toList

    val res = (
      "digraph " + program.id.name + " {\n" +
      vertexLabels.map(p => p._1 + " [label=\"" + p._2 + "\"];").mkString("\n") + "\n" +
      edges.map(p => p._1 + " -> " + p._2 + " [label=\"" + p._3 + "\"];").mkString("\n") + "\n" +
      "}")

    res
  }

  def toString(inferences: Array[Inference]): String = {

  }

}
