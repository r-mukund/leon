import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Complete {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List) : Int = (l match {
      case Nil => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list : List) : Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  // def insert2(in1: List, v: Int): List = {
  //   require(isSorted(in1))
  //   in1 match {
  //     case Cons(h, t) =>
  //       if (v < h) {
  //         Cons(v, in1)
  //       } else if (v == h) {
  //         Cons(v, in1)
  //       } else {
  //         Cons(h, insert2(t, v))
  //       }
  //     case Nil =>
  //       Cons(v, Nil)
  //   }
  // } ensuring { res => (content(res) == content(in1) ++ Set(v)) && isSorted(res) && size(res) == size(in1) + 1 }

  def insert2(in1: List, v: Int) = {
    require(isSorted(in1))

    choose {
      (out : List) =>
        (content(out) == content(in1) ++ Set(v)) && isSorted(out) && size(out) == size(in1) + 1
    }
  }

}
