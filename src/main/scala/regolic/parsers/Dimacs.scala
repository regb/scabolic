package regolic.parsers

import scala.io.Source
import java.io.InputStream

import regolic.sat.Solver.Var
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

object Dimacs {
  
  def apply(input: InputStream): List[Formula] = {

    var formulas: List[Formula] = List()
    var vars: Array[PredicateApplication] = null
    var nbClauses: Option[Int] = None

    for(line <- Source.fromInputStream(input).getLines()) {
      val length = line.size
      if(length > 0 && line(0) != 'c' && line(0) != '%') {
        if(line.startsWith("p cnf")) {

          if(vars != null || nbClauses != None)
            throw new FileFormatException("A line starting with 'p cnf' is defined twice")

          val rest = line.substring("p cnf".length, length).split(' ').filterNot(_ == "")
          try {
            val restInts = rest.map(_.toInt)
            if(restInts.size != 2)
              throw FileFormatException("")
            val nbVariables = restInts(0)
            nbClauses = Some(restInts(1))
            vars = new Array(nbVariables)
            for(i <- 0 until nbVariables)
              vars(i) = Var("x" + i)
          } catch {
            case (_: NumberFormatException) => throw FileFormatException("")
          }

        } else { //should be a clause
          if(vars == null || nbClauses == None)
            throw new FileFormatException("A line starting with 'p cnf' should occur before any clauses")

          try {
            val numbers = line.split(' ').filterNot(_ == "").map(_.toInt)
            if(numbers.last != 0)
              throw new FileFormatException("A clause line should end with a 0")

            val varNumbers = numbers.init
            if(!varNumbers.isEmpty)
              formulas ::= Or(varNumbers.map(i => if(i > 0) vars(i-1) else Not(vars(-i-1))).toList)

          } catch {
            case (_: NumberFormatException) => throw FileFormatException("")
          }
          

        }
      } //else simply ignore the line, don't need to reject the input file for that
    }

    formulas
  }

}
