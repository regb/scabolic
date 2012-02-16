package regolic.asts.fol

import regolic.asts.fol.Trees._
import regolic.tools.Math.fix
import regolic.asts.core.Manip._
import regolic.asts.core.Trees.Formula
import regolic.asts.core.Trees.PredicateApplication

object Manip {

  def simplify(formula: Formula): Formula = {
    def simplifyOne(f: Formula): Formula = {
      def simplifyOneNot(f: Formula): Formula = f match {
        case Not(Not(f)) => f
        case Not(True()) => False()
        case Not(False()) => True()
        case f@_ => f match {
          case Not(And(fs)) => {
            val nbn = fs.count(isNot)
            val nbr = fs.length - nbn
            if(nbn >= nbr)
              Or(fs.map{ case Not(f) => f case f@_ => Not(f) })
            else
              f
          }
          case Not(Or(fs)) => {
            val nbn = fs.count(isNot)
            val nbr = fs.length - nbn
            if(nbn >= nbr)
              And(fs.map{ case Not(f) => f case f@_ => Not(f) })
            else
              f
          }
          case _ => f
        }
      }
      def simplifyOneAnd(f: Formula): Formula = f match {
        case And(Nil) => True()
        case And(f :: Nil) => f
        case And(fs) if fs.exists(isFalse) => False()
        case And(fs) if fs.exists(isTrue) => And(fs.filterNot(isTrue))
        case And(fs) => {
          val nfs = fs.flatMap({ case And(fs2) => fs2 case f2 => List(f2)})
          val nbn = nfs.count(isNot)
          val nbr = nfs.length - nbn
          if(nbn > nbr + 1)
            Not(Or(nfs.map{ case Not(f) => f case f@_ => Not(f) }))
          else
            And(nfs)
        }
        case f@_ => f
      }
      def simplifyOneOr(f: Formula): Formula = f match {
        case Or(Nil) => False()
        case Or(f :: Nil) => f
        case Or(f1 :: Not(f2) :: Nil) =>  Implies(f2, f1)
        case Or(Not(f1) :: f2 :: Nil) =>  Implies(f1, f2)
        case Or(fs) if fs.exists(isTrue) => True()
        case Or(fs) if fs.exists(isFalse) => Or(fs.filterNot(isFalse))
        case Or(fs) => {
          val nfs = fs.flatMap({ case Or(fs2) => fs2 case f2 => List(f2)})
          val nbn = nfs.count(isNot)
          val nbr = nfs.length - nbn
          if(nbn > nbr + 1)
            Not(And(nfs.map{ case Not(f) => f case f@_ => Not(f) }))
          else
            Or(nfs)
        }
        case f@_ => f
      }
      def simplifyOneIfThenElse(f: Formula): Formula = f match {
        case IfThenElse(True(), f, _) => f
        case IfThenElse(False(), _, f) => f
        case IfThenElse(_, True(), True()) => True()
        case IfThenElse(_, False(), False()) => False()
        case f@_ => f
      }
      def simplifyOneImplies(f: Formula): Formula = f match {
        case Implies(False(), _) => True()
        case Implies(_, True()) => True()
        case Implies(f, False()) => Not(f)
        case Implies(True(), f) => f
        case Implies(Not(f1), f2) => Or(List(f1, f2))
        case f@_ => f
      }
      def simplifyOneIff(f: Formula): Formula = f match {
        case Iff(False(), True()) => False()
        case Iff(False(), False()) => True()
        case Iff(False(), f) => Not(f)
        case Iff(True(), True()) => True()
        case Iff(True(), False()) => False()
        case Iff(True(), f) => f
        case Iff(f, False()) => Not(f)
        case Iff(f, True()) => f
        case f@_ => f
      }

      f match {
        case Not(_) => simplifyOneNot(f)
        case And(_) => simplifyOneAnd(f)
        case Or(_) => simplifyOneOr(f)
        case Implies(_,_) => simplifyOneImplies(f)
        case Iff(_,_) => simplifyOneIff(f)
        case IfThenElse(_,_,_) => simplifyOneIfThenElse(f)
        case f@_ => f
      }
    }

    def mapSimplify(f: Formula): Formula = mapPostorder(f, simplifyOne, x => x)

    fix(mapSimplify,formula)
  }

  //a conjunctive normal form, always as an And of Ors (even with single formula)
  def isConjunctiveNormalForm(formula: Formula): Boolean = formula match {
    case And(fs) => fs.forall{
      case Or(fs2) => fs2.forall(f => f match {
        case Not(PredicateApplication(_, _)) => true
        case PredicateApplication(_, _) => true
        case _ => false
      })
      case _ => false
    }
    case _ => false
  }
  def conjunctiveNormalForm(formula: Formula): Formula = {
    require(isQuantifierFree(formula))

    def distribute(and1: Formula, and2: Formula): Formula = {
      val (And(fs1), And(fs2)) = (and1, and2)
      And(fs1.flatMap{ case Or(fss1) =>
        fs2.map{ case Or(fss2) => Or(fss1 ::: fss2) }
      })
    }

    def inductiveStep(f: Formula): Formula = f match {
      case And(fs) => fs match {
        case Nil => And(List(Or(List(False()))))
        case fs => And(fs.flatMap{ case And(fs2) => fs2 })
      }
      case Or(fs) => fs match {
        case Nil => And(List(Or(List(True()))))
        case f::Nil => f
        case fs => And(
          fs.reduceLeft((and1, and2) => distribute(and1, and2)) match {
            case And(fs2) => fs2
          }
        )
      }
      case Not(And(fs)) => inductiveStep(Or(fs.map{
        case Or(fs2) => And(fs2.map{ //I map to an Or so that each element is in cnf
          case Not(f) => Or(List(f))
          case f => Or(List(Not(f)))
        })
      }))

      case p@PredicateApplication(_, _) => And(List(Or(List(p))))

      case _ => sys.error("unexpected formula: " + f)

    }

    mapPostorder(basicForm(formula), inductiveStep, t => t)
  }

  //basic form is form containing only quantifiers with And, Or and Not connectives
  def isBasicForm(formula: Formula): Boolean = forall(formula, (f: Formula) => f match {
    case Iff(_, _) | Implies(_, _) | IfThenElse(_, _, _) => false
    case _ => true
  })
  def basicForm(formula: Formula): Formula = {
    def inductiveStep(f: Formula): Formula = f match {
      case Iff(f1, f2) => Or(List(And(List(f1, f2)), And(List(Not(f1), Not(f2)))))
      case Implies(f1, f2) => Or(List(f2, Not(f1)))
      case IfThenElse(f1, f2, f3) => And(List(Or(List(Not(f1), f2)), Or(List(f1, f3)))) //TODO: I'm not so sure about the meaning of IfThenElse
      case _ => f
    }

    mapPostorder(formula, inductiveStep, t => t)
  }

  def isQuantifierFree(f: Formula): Boolean = forall(f, (sf: Formula) => sf match {
      case Forall(_, _) | Exists(_, _) => false
      case _ => true
    })

  private def isTrue(f: Formula) = f match {
    case True() => true
    case _ => false
  }
  private def isFalse(f: Formula) = f match {
    case False() => true
    case _ => false
  }
  private def isNot(f: Formula) = f match {
    case Not(_) => true
    case _ => false
  }
}
