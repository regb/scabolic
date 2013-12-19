package regolic
package cafesat

import dpllt._
import DPLLSolver.Results._

import util.Logger

import asts.core.Manip._
import asts.core.Trees._
import asts.fol.Trees._
import asts.fol.Manip._

/* TODO: just an idea, could we abstract the formula Type 
 * and provide a function to map formula to CNF with 
 * literals usable by theory solver ?
 */

import scala.collection.mutable.HashMap

class Solver(implicit val context: Context) {

  private val logger = context.logger
  private implicit val tag = Logger.Tag("Solver Interface")
  type Model = Map[FunctionApplication, Term]

  private var asserts: List[Formula] = List(True())
  private var isModelAvailable = false
  private var currentModel: Model = _

  def pop(numScopes: Int = 1): Unit = {
    if(numScopes > (asserts.size - 1))
      throw new Exception("Poping empty scope")
    asserts = asserts.drop(numScopes)
  }

  def push(): Unit = {
    asserts ::= True()
  }

  def assertCnstr(f: Formula): Unit = {
    asserts = And(f, asserts.head) :: asserts.tail
  }

  def check(): Option[Boolean] = {
    val res = try {
      checkSat()
    } catch {
      case (e: Exception) => {
        logger.warning("Could not check consistency of the formula: " + e.getMessage)
        None
      }
    }
    isModelAvailable = res == Some(true)
    res
  }

  private def checkSat(): Option[Boolean] = {
    val qfeufComponent = new qfeuf.Component
    val theoryComponent = new TheoryWithBoolean[qfeufComponent.type](qfeufComponent)
    val formula: Formula = simplify(asserts.foldLeft(True(): Formula)((acc, f) => And(acc, f)))

    val boolSort = Sort("BoolFakeSort", List())
    val boolConst = FunctionApplication(FunctionSymbol("BoolConst", Nil, boolSort), Nil)
    val predToFun: HashMap[PredicateSymbol, FunctionSymbol] = new HashMap
    val formulaWithoutPreds = mapPreorder(formula, (f: Formula) => f match { 
      case Equals(_, _) => f
      case Not(Equals(_, _)) => f
      case PredicateApplication(sym, args) => predToFun.get(sym) match {
        case Some(s) => Equals(FunctionApplication(s, args), boolConst)
        case None => {
          val freshSym = freshFunctionSymbol(sym.name, sym.argSorts, boolSort)
          predToFun(sym) = freshSym
          Equals(FunctionApplication(freshSym, args), boolConst)
        }
      }
      case Not(PredicateApplication(sym, args)) => predToFun.get(sym) match {
        case Some(s) => Not(Equals(FunctionApplication(s, args), boolConst))
        case None => {
          val freshSym = freshFunctionSymbol(sym.name, sym.argSorts, boolSort)
          predToFun(sym) = freshSym
          Not(Equals(FunctionApplication(freshSym, args), boolConst))
        }
      }
      case f => f
    }, (t: Term) => t)

    val currified: Formula = mapPreorder(formulaWithoutPreds, f => f, t => qfeuf.Currifier(t))
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

    result match {
      case Satisfiable(model) => {
        //currentModel = model
        Some(true)
      }
      case Unsatisfiable => Some(false)
      case Unknown => None
    }
  }

  def getModel(): Model =
    if (isModelAvailable)
      currentModel
    else
      throw new Exception("Cannot get model if check failed")

  /*
  def getProof() : Z3AST = {
    if (!isModelAvailable) {
      new Z3AST(Z3Wrapper.solverGetProof(context.ptr, this.ptr), context)
    } else {
      throw new Exception("Cannot get proof if formula is SAT")
    }
  }

  def getUnsatCore() : Z3ASTVector = {
    new Z3ASTVector(Z3Wrapper.solverGetUnsatCore(context.ptr, this.ptr), context)
  }

  def reset() = {
    Z3Wrapper.solverReset(context.ptr, this.ptr)
  }
  */

  /*
  def checkAssumptions(assumptions: Z3AST*) : Option[Boolean] = {
    val res = i2ob(
      Z3Wrapper.solverCheckAssumptions(
        context.ptr,
        this.ptr,
        assumptions.size,
        toPtrArray(assumptions)
      )
    )

    isModelAvailable = res != Some(false)
    res
  }
  */

}
