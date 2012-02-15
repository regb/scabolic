package regolic.tools

object SeqTools {

  def mapUnique[A](f: (A) => Option[A], seq: Seq[A]): Seq[A] = {
    var found = false
    seq.map(el => if(found) el else
      f(el) match {
        case None => el
        case Some(nel) => {
          found = true
          nel
        }
      })
    }

  def mapUnique[A](f: (A) => Option[A], list: List[A]): List[A] = {
    var found = false
    list.map(el => if(found) el else
      f(el) match {
        case None => el
        case Some(nel) => {
          found = true
          nel
        }
      })
    }
}
