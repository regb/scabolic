package regolic
package smtlib

import parsers.SmtLib2._
import parsers.SmtLib2.Trees._
import sexpr.SExprs._

import dpllt.TheorySolver
import dpllt.Solver.Results._
import smt.qfeuf._

import util._

import asts.core.Manip._
import asts.core.Trees._
import asts.fol.Trees._
import asts.fol.Manip._

object Eval {

  object SolverFactory {
    def apply(logic: Logic) = {
      logic match {
        case QF_UF => Some(new FastCongruenceClosure)
        case _ => {
          println("Logic not supported.")
          None
        }
      }
    }
  }

  def execute(cmds: List[Command]): Unit = {
    //var solver: Option[TheorySolver] = None
    var solver: Option[FastCongruenceClosure] = None
    var asserts: List[Formula] = List(True())

    var expectedResult: Option[Boolean] = None

    for(cmd <- cmds) {
      cmd match {
        case SetLogic(logic) => solver = SolverFactory(logic)
        case Pop(n) => {
          asserts = asserts.tail
        }
        case Push(n) => {
          asserts ::= True()
        }
        case Assert(f) => {
          asserts = And(f, asserts.head) :: asserts.tail
        }
        case CheckSat => {
          if(solver != None) {
            val formula: Formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))
            val currified: Formula = mapPreorder(formula, f => f, t => Currifier(t))
            val (flattened, eqs) = Flattener.transform(currified)
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
            def builder(p: PredicateApplication, id: Int, pol: Boolean): smt.qfeuf.Literal = {
              val Equals(FunctionApplication(a, Nil), FunctionApplication(b, Nil)) = p
              val aId = constantsToId(a.name)
              val bId = constantsToId(b.name)
              smt.qfeuf.Literal(Left(aId, bId), id, pol, p)
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

            val (cnf, nbLits, mapping) = dpllt.PropositionalSkeleton(withoutVars, builder)

            import sexpr.SExprs._
            val smtLibProblem: List[SExpr] = 
              SList(List(SSymbol("set-logic"), SSymbol("QF_UF"))) ::
              SList(List(SSymbol("declare-sort"), SSymbol("U"), SInt(0))) ::
              SList(List(SSymbol("declare-fun"), SSymbol("apply"), SList(List(SSymbol("U"), SSymbol("U"))), SList(List(SSymbol("U"))))) ::
              (for(i <- 0 until constantsToId.nbConstants) yield 
                SList(List(SSymbol("declare-fun"), SSymbol("c_" + i), SList(Nil), SSymbol("U")))).toList :::
              (for(i <- 0 until nbLits) yield 
                SList(List(SSymbol("declare-fun"), SSymbol("p_" + i), SList(Nil), SSymbol("Bool")))).toList :::
              SList(List(SSymbol("assert"), printers.SmtLib2.conjunctionToSExpr(toMerge.map(t => smt.qfeuf.Literal(Right(t), 0, true, null)).toSet))) ::
              //SList(List(SSymbol("assert"), printers.SmtLib2.cnfToSExpr( cnf))) ::
              //SList(List(SSymbol("check-sat"))) ::
              Nil

            //println(smtLibProblem.map(sexpr.PrettyPrinter(_)).mkString("\n"))

            //logger.debug("Apply: %s", toMerge.mkString("{\n\t", "\n\t", "}"))
            //logger.debug("Mapping: %s", mapping.mkString("{\n\t", "\n\t", "}"))

            val cc = Settings.logLevel match {
              case Logger.LogLevel.Warning => new FastCongruenceClosure with HasDefaultStdErrLogger
              case Logger.LogLevel.Debug => new FastCongruenceClosure with HasVerboseStdErrLogger
              case Logger.LogLevel.Trace => new FastCongruenceClosure with HasTraceStdErrLogger
            }
            cc.initialize(cnf.flatten)
            toMerge.foreach{ case (a1, a2, a) => cc.merge(a1, a2, a) }

            val ccConfirm = Settings.logLevel match {
              case Logger.LogLevel.Warning => new FastCongruenceClosure with HasDefaultStdErrLogger
              case Logger.LogLevel.Debug => new FastCongruenceClosure with HasVerboseStdErrLogger
              case Logger.LogLevel.Trace => new FastCongruenceClosure with HasTraceStdErrLogger
            }
            ccConfirm.initialize(cnf.flatten)
            toMerge.foreach{ case (a1, a2, a) => ccConfirm.merge(a1, a2, a) }

            val solver = new dpllt.Solver(nbLits, cc)
            cnf.foreach(clause => solver.addClause(clause))

            val result = solver.solve()

            val resultString = result match {
              case Satisfiable(model) => {
                val literals: Array[dpllt.Literal] = Array.fill(2*nbLits)(null)
                cnf.foreach(clause => clause.foreach(lit => literals(2*lit.id + lit.polInt) = lit))
                model.zipWithIndex.foreach{ case (pol, id) => {
                  val tLit = literals(2*id + (if(pol) 1 else 0))
                  if(tLit.isInstanceOf[smt.qfeuf.Literal])
                    ccConfirm.setTrue(tLit)
                }}
                if(expectedResult == Some(false))
                  "sat | should be unsat"
                else
                  "sat"
              }           
              case Unsatisfiable if expectedResult == Some(true) => "unsat | should be sat"
              case Unsatisfiable => "unsat"
            }
            println(resultString)
          } else println("Solver not set.")
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
