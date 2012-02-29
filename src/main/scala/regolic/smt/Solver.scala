package regolic.smt

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

trait Solver {

  def isSat(f: Formula): Option[Map[Variable, Term]]

}
