package regolic
package smtlib

import regolic.sexpr
import regolic.sexpr.SExprs._

object Commands {

  sealed abstract class Command
  case class SetLogic(logic: Logic) extends Command
  case class SetOption(attribute: Attribute) extends Command //TODO: option instead of attribute
  case class SetInfo(attribute: Attribute) extends Command
  case class DeclareSort(name: SSymbol, arity: Int) extends Command
  //case class DefineSort
  case class DeclareFun(name: SSymbol, paramSorts: Seq[SExpr], returnSort: SExpr) extends Command
  //case class DefineFun
  case class Assert(term: SExpr) extends Command
  case class Push(n: Int) extends Command
  case class Pop(n: Int) extends Command
  case object CheckSat extends Command
  case object GetProof extends Command
  case object GetUnsatCore extends Command
  case object Exit extends Command

  case class Attribute(name: String, v: Option[SExpr])

  sealed abstract trait Logic
  case object QF_UF extends Logic
  case object QF_LRA extends Logic
  case object QF_AX extends Logic
  case object QF_A extends Logic
  case object Undef extends Logic

  object Logic {
    def fromString(logic: String): Logic = logic match {
      case "QF_UF"  => QF_UF
      case "QF_LRA" => QF_LRA
      case "QF_AX"  => QF_AX
      case "QF_A"   => QF_A
    }
  }

  abstract sealed trait CommandResponse

}
