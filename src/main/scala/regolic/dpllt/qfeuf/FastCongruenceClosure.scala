package regolic
package dpllt
package qfeuf 

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import util.{HasLogger, Logger}

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer

  //class PreProcessing {
  //
  //  def apply(cnf: Set[Set[Formula]]): Set[Set[smt.Literal]] = {
  //
  //    var namesToConstants: Map[String, Int] = {
  //      var constantId = -1
  //      new HashMap[String, Int] {
  //        override def apply(name: String): Int = this.get(name) match {
  //          case Some(id) => id
  //          case None => {
  //            constantId += 1
  //            this(name) = constantId
  //            constantId
  //          }
  //        }
  //      }
  //    }
  //
  //    var extraDefs: List[FastCongruenceClosure.InputEquation] = List()
  //
  //    def addName(p: (String, FunctionApplication)): Unit = p match {
  //      case (a, Apply(FunctionApplication(FunctionSymbol(a1, _, _), _), FunctionApplication(FunctionSymbol(a2, _, _), _))) =>
  //        extraDefs ::= Right((namesToConstants(a1), namesToConstants(a2), namesToConstants(a)))
  //      case (a, FunctionApplication(FunctionSymbol(b, _, _), _)) =>
  //        extraDefs ::= Left((namesToConstants(a), namesToConstants(b)))
  //    }
  //
  //    val processed: List[List[smt.Literal]] = cnf.toList.map(clause => clause.toList.map(lit => lit match {
  //      case eq@Equals(t1, t2) => {
  //        val ct1 = Currifier(t1)
  //        val ct2 = Currifier(t2)
  //        val (Variable(name1, _), names1) = Flattener.transform(ct1)
  //        val (Variable(name2, _), names2) = Flattener.transform(ct2)
  //        names1.foreach(p => addName(p))
  //        names2.foreach(p => addName(p))
  //        Literal(
  //          Left((namesToConstants(name1), namesToConstants(name2))),
  //          0,
  //          true,
  //          eq
  //        )
  //
  //      }
  //      case Not(eq@Equals(t1, t2)) => {
  //        val ct1 = Currifier(t1)
  //        val ct2 = Currifier(t2)
  //        val (Variable(name1, _), names1) = Flattener.transform(ct1)
  //        val (Variable(name2, _), names2) = Flattener.transform(ct2)
  //        names1.foreach(p => addName(p))
  //        names2.foreach(p => addName(p))
  //        Literal(
  //          Left((namesToConstants(name1), namesToConstants(name2))),
  //          0,
  //          false,
  //          eq
  //        )
  //      }
  //    }))
  //
  //    processed.map(clause => clause.toSet).toSet ++ extraDefs.map(ie => Set[smt.Literal](Literal(ie, 0, true, null))).toSet
  //
  //  }
  //
  //}
