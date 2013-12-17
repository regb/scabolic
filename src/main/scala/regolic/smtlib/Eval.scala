package regolic
package smtlib

import parsers.SmtLib2._
import parsers.SmtLib2.Trees._
import sexpr.SExprs._

import dpllt._
import DPLLSolver.Results._

import util._

import asts.core.Manip._
import asts.core.Trees._
import asts.fol.Trees._
import asts.fol.Manip._

object Eval {

  //object SolverFactory {
  //  def apply(logic: Logic) = {
  //    logic match {
  //      case QF_UF => Some(new FastCongruenceClosure)
  //      case _ => {
  //        println("Logic not supported.")
  //        None
  //      }
  //    }
  //  }
  //}

  //def execute(cmds: List[Command])(implicit context: Context): Unit = ???
  def execute(cmds: List[Command])(implicit context: Context): Unit = {
    var asserts: List[Formula] = List(True())
    var expectedResult: Option[Boolean] = None

    for(cmd <- cmds) {
      cmd match {
        case SetLogic(logic) => () //solver = SolverFactory(logic)
        case Pop(n) => {//TODO: what is n ?
          asserts = asserts.tail
        }
        case Push(n) => {//TODO: what is n ?
          asserts ::= True()
        }
        case Assert(f) => {
          asserts = And(f, asserts.head) :: asserts.tail
        }
        case CheckSat => {
          val qfeufComponent = new qfeuf.Component
          val theoryComponent = new TheoryWithBoolean[qfeufComponent.type](qfeufComponent)
          val formula: Formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))
          val currified: Formula = mapPreorder(formula, f => f, t => qfeuf.Currifier(t))
          val (flattened, eqs) = qfeuf.Flattener.transform(currified)
          val withoutVars: Formula = mapPreorder(flattened, f => f, { case Variable(v, s) => FunctionApplication(FunctionSymbol(v, Nil, s), Nil) case t => t })
          //println("flatten: " + flattened)
          //println("eqs: " + eqs)

          import scala.language.reflectiveCalls
          //TODO: this hashmap seems to be a recuring pattern
          val constantsToId = {
            var constantId = -1
            new scala.collection.mutable.HashMap[String, Int] {
              override def apply(cst: String): Int = get(cst) match {
                case Some(id) => id
                case None => {
                  constantId += 1
                  update(cst, constantId)
                  constantId
                }
              }

              def nbConstants = constantId + 1
            }
          }
          def builder(p: PredicateApplication, id: Int, pol: Boolean): theoryComponent.Literal = {
            val Equals(FunctionApplication(a, Nil), FunctionApplication(b, Nil)) = p
            val aId = constantsToId(a.name)
            val bId = constantsToId(b.name)
            theoryComponent.Lit(Right(qfeufComponent.Lit(aId, bId, id, pol, p)))
          }
          val toMerge: List[(Int, Int, Int)] = eqs.map{ 
            case (cst, FunctionApplication(apply, a::b::Nil)) => {
              val aName = a match {
                case Variable(n, _) => n
                case FunctionApplication(s, Nil) => s.name
              }
              val bName = b match {
                case Variable(n, _) => n
                case FunctionApplication(s, Nil) => s.name
              }
              (constantsToId(aName), constantsToId(bName), constantsToId(cst))
            }
          }.toList

          val propSkeleton = new dpllt.PropositionalSkeleton[theoryComponent.type](theoryComponent)
          val (cnf, nbLits, mapping) = propSkeleton(withoutVars, theoryComponent.makePropLit, builder)

          //import sexpr.SExprs._
          //val smtLibProblem: List[SExpr] = 
          //  SList(List(SSymbol("set-logic"), SSymbol("QF_UF"))) ::
          //  SList(List(SSymbol("set-info"), SSymbol(":smt-lib-version 2.0"))) ::
          //  SList(List(SSymbol("declare-sort"), SSymbol("U"), SInt(0))) ::
          //  SList(List(SSymbol("declare-fun"), SSymbol("apply"), SList(List(SSymbol("U"), SSymbol("U"))), SList(List(SSymbol("U"))))) ::
          //  (for(i <- 0 until constantsToId.nbConstants) yield 
          //    SList(List(SSymbol("declare-fun"), SSymbol("c_" + i), SList(Nil), SSymbol("U")))).toList :::
          //  (for(i <- 0 until nbLits) yield 
          //    SList(List(SSymbol("declare-fun"), SSymbol("p_" + i), SList(Nil), SSymbol("Bool")))).toList :::
          //  SList(List(SSymbol("assert"), printers.SmtLib2.conjunctionToSExpr(toMerge.map(t => smt.qfeuf.Literal(Right(t), 0, true, null)).toSet))) ::
          //  SList(List(SSymbol("assert"), printers.SmtLib2.cnfToSExpr(cnf))) ::
          //  SList(List(SSymbol("check-sat"))) ::
          //  Nil

          //println(smtLibProblem.map(sexpr.PrettyPrinter(_)).mkString("\n"))

          //logger.debug("Apply: %s", toMerge.mkString("{\n\t", "\n\t", "}"))
          //logger.debug("Mapping: %s", mapping.mkString("{\n\t", "\n\t", "}"))

          val tSolver = theoryComponent.makeSolver(cnf)
          val cc = tSolver.s2
          //cc.initialize(cnf.flatten)
          toMerge.foreach{ case (a1, a2, a) => cc.merge(a1, a2, a) }

          val solver = new dpllt.DPLLSolver[theoryComponent.type](nbLits, theoryComponent)
          cnf.foreach(clause => solver.addClause(clause))

          val result = solver.solve(tSolver)

          val resultString = result match {
            case Satisfiable(model) => {
              if(expectedResult == Some(false))
                "sat | should be unsat"
              else
                "sat"
            }           
            case Unsatisfiable if expectedResult == Some(true) => "unsat | should be sat"
            case Unsatisfiable => "unsat"
          }
          println(resultString)
        }
        case SetInfo(attr) => {
          attr match {
            case Attribute("STATUS", Some(SSymbol("SAT"))) => expectedResult = Some(true)
            case Attribute("STATUS", Some(SSymbol("UNSAT"))) => expectedResult = Some(false)
            case Attribute("STATUS", _) => {
              println("WARNING: set-info status set to unsupported value")
              expectedResult = None
            }
            // TODO
            case Attribute("SOURCE", Some(SSymbol(src))) => ()
            case Attribute("SMT-LIB-VERSION", Some(SDouble(ver))) => ()
            case Attribute("CATEGORY", Some(SString(cat))) => ()
            case _ => println("WARNING: unsupported set-info attribute")
          }
        }
        case Exit => {
          sys.exit()
        }
      }
    }

  }

}
