object Uint32 {

def less(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Int, n: BigInt, b: Boolean) : Int =
  if (b)
    x | (1 << n.intValue)
  else
    x & (1 << n.intValue).unary_~

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint32 */


object DiffArray {

  import scala.collection.mutable.ArraySeq

  protected abstract sealed class DiffArray_D[A]
  final case class Current[A] (a:ArraySeq[A]) extends DiffArray_D[A]
  final case class Upd[A] (i:Int, v:A, n:DiffArray_D[A]) extends DiffArray_D[A]

  object DiffArray_Realizer {
    def realize[A](a:DiffArray_D[A]) : ArraySeq[A] = a match {
      case Current(a) => ArraySeq.empty ++ a
      case Upd(j,v,n) => {val a = realize(n); a.update(j, v); a}
    }
  }

  class T[A] (var d:DiffArray_D[A]) {

    def realize () = { val a=DiffArray_Realizer.realize(d); d = Current(a); a }
    override def toString() = realize().toSeq.toString

    override def equals(obj:Any) =
      if (obj.isInstanceOf[T[A]]) obj.asInstanceOf[T[A]].realize().equals(realize())
      else false

  }


  def array_of_list[A](l : List[A]) : T[A] = new T(Current(ArraySeq.empty ++ l))
    def new_array[A](v:A, sz : BigInt) = new T[A](Current[A](ArraySeq.fill[A](sz.intValue)(v)))

    private def length[A](a:DiffArray_D[A]) : BigInt = a match {
    case Current(a) => a.length
    case Upd(_,_,n) => length(n)
  }

  def length[A](a : T[A]) : BigInt = length(a.d)

  private def sub[A](a:DiffArray_D[A], i:Int) : A = a match {
    case Current(a) => a (i)
    case Upd(j,v,n) => if (i==j) v else sub(n,i)
  }

  def get[A](a:T[A], i:BigInt) : A = sub(a.d,i.intValue)

  private def realize[A](a:DiffArray_D[A]) = DiffArray_Realizer.realize[A](a)

  def set[A](a:T[A], i:BigInt,v:A) : T[A] = a.d match {
    case Current(ad) => {
      val ii = i.intValue;
      a.d = Upd(ii,ad(ii),a.d);
      //ad.update(ii,v);
      ad(ii)=v
      new T[A](Current(ad))
    }
    case Upd(_,_,_) => set(new T[A](Current(realize(a.d))), i.intValue,v)
  }

  def grow[A](a:T[A], sz:BigInt, v:A) : T[A] = a.d match {
    case Current(ad) => {
      val adt = ArraySeq.fill[A](sz.intValue)(v)
      System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
      new T[A](Current[A](adt))
    }
    case Upd (_,_,_) =>  {
      val adt = ArraySeq.fill[A](sz.intValue)(v)
      val ad = realize(a.d)
      System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
      new T[A](Current[A](adt))
    }
  }

  def shrink[A](a:T[A], sz:BigInt) : T[A] =
    if (sz==0) {
      array_of_list(Nil)
    } else {
      a.d match {
        case Current(ad) => {
            val v=ad(0);
            val szz=sz.intValue
          val adt = ArraySeq.fill[A](szz)(v);
          System.arraycopy(ad.array, 0, adt.array, 0, szz);
          new T[A](Current[A](adt))
        }
        case Upd (_,_,_) =>  {
          val ad = realize(a.d);
            val szz=sz.intValue
            val v=ad(0);
          val adt = ArraySeq.fill[A](szz)(v);
          System.arraycopy(ad.array, 0, adt.array, 0, szz);
          new T[A](Current[A](adt))
        }
      }
    }

  def get_oo[A](d: => A, a:T[A], i:BigInt):A = try get(a,i) catch {
    case _:scala.IndexOutOfBoundsException => d
  }

  def set_oo[A](d: Unit => T[A], a:T[A], i:BigInt, v:A) : T[A] = try set(a,i,v) catch {
    case _:scala.IndexOutOfBoundsException => d ()
  }

}

/*
object Test {



  def assert (b : Boolean) : Unit = if (b) () else throw new java.lang.AssertionError("Assertion Failed")

  def eql[A] (a:DiffArray.T[A], b:List[A]) = assert (a.realize.corresponds(b)((x,y) => x.equals(y)))


  def tests1(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Another update
    val c = DiffArray.set(b,3,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)

    // Update of old version (forces realize)
    val d = DiffArray.set(b,2,8)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)
      eql(d,1::2::8::4::Nil)

    }

  def tests2(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Grow of current version
    val c = DiffArray.grow(b,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)

    // Grow of old version
    val d = DiffArray.grow(a,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)
      eql(d,1::2::3::4::9::9::Nil)

  }

  def tests3(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Shrink of current version
    val c = DiffArray.shrink(b,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)

    // Shrink of old version
    val d = DiffArray.shrink(a,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)
      eql(d,1::2::3::Nil)

  }

  def tests4(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update _oo (succeeds)
    val b = DiffArray.set_oo((_) => a,a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Update _oo (current version,fails)
    val c = DiffArray.set_oo((_) => a,b,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)

    // Update _oo (old version,fails)
    val d = DiffArray.set_oo((_) => b,a,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)
      eql(d,1::2::9::4::Nil)

  }

  def tests5(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Get_oo (current version, succeeds)
      assert (DiffArray.get_oo(0,b,2)==9)
    // Get_oo (current version, fails)
      assert (DiffArray.get_oo(0,b,5)==0)
    // Get_oo (old version, succeeds)
      assert (DiffArray.get_oo(0,a,2)==3)
    // Get_oo (old version, fails)
      assert (DiffArray.get_oo(0,a,5)==0)

  }




  def main(args: Array[String]): Unit = {
    tests1 ()
    tests2 ()
    tests3 ()
    tests4 ()
    tests5 ()


    Console.println("Tests passed")
  }

}*/



object Bits_Integer {

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt) 
  else
    sys.error("Bit index too large: " + n.toString)

} /* object Bits_Integer */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
}

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Map {

def map_of[A : HOL.equal, B](x0: List[(A, B)], k: A): Option[B] = (x0, k) match
  {
  case ((l, v) :: ps, k) =>
    (if (HOL.eq[A](l, k)) Some[B](v) else map_of[A, B](ps, k))
  case (Nil, k) => None
}

} /* object Map */

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

} /* object Nat */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
object ord {
  implicit def `Uint32a.ord_uint32`: ord[Int] = new ord[Int] {
    val `Orderings.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `Orderings.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def `Uint32a.preorder_uint32`: preorder[Int] = new preorder[Int] {
    val `Orderings.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `Orderings.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `Uint32a.order_uint32`: order[Int] = new order[Int] {
    val `Orderings.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `Orderings.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def `Uint32a.linorder_uint32`: linorder[Int] = new linorder[Int] {
    val `Orderings.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `Orderings.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
}

} /* object Orderings */

object RBT_Impl {

abstract sealed class color
final case class R() extends color
final case class B() extends color

abstract sealed class rbt[A, B]
final case class Empty[A, B]() extends rbt[A, B]
final case class Branch[A, B](a: color, b: rbt[A, B], c: A, d: B, e: rbt[A, B])
  extends rbt[A, B]

def paint[A, B](c: color, x1: rbt[A, B]): rbt[A, B] = (c, x1) match {
  case (c, Empty()) => Empty[A, B]()
  case (c, Branch(uu, l, k, v, r)) => Branch[A, B](c, l, k, v, r)
}

def balance[A, B](x0: rbt[A, B], s: A, t: B, x3: rbt[A, B]): rbt[A, B] =
  (x0, s, t, x3) match {
  case (Branch(R(), a, w, x, b), s, t, Branch(R(), c, y, z, d)) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(B(), va, vb, vc, vd), w, x, Branch(R(), b, s, t, c)),
         y, z, Empty())
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Branch(B(), ve, vf, vg, vh), w, x, Branch(R(), b, s, t, c)),
         y, z, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), ve, vf, vg, vh), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Empty(), w, x, Branch(R(), b, s, t, Branch(R(), c, y, z, d))) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), b, s, t, Branch(R(), c, y, z, d)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, d))
  case (Empty(), w, x, Branch(R(), Branch(R(), b, s, t, c), y, z, Empty())) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Empty(), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), va, vb, vc, vd)))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z, Empty()))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), ve, vf, vg, vh)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), ve, vf, vg, vh)))
  case (Empty(), s, t, Empty()) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Empty[A, B]())
  case (Empty(), s, t, Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Empty())) =>
    Branch[A, B](B(), Empty[A, B](), s, t,
                  Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Branch(B(), ve, vf, vg, vh), vb, vc, Empty()))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vf, vg, vh), vb, vc,
                                   Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Empty[A, B](), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Empty(), s, t,
         Branch(v, Branch(B(), ve, vj, vk, vl), vb, vc,
                 Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vj, vk, vl), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Branch(B(), va, vb, vc, vd), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t, Empty[A, B]())
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(B(), ve, vf, vg, vh)) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                  Branch[A, B](B(), ve, vf, vg, vh))
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(v, Empty(), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vj, vk, vl), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vj, vk, vl), vf, vg,
                                   Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Empty(), vf, vg, Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vn, vo, vp), vf, vg,
                 Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vn, vo, vp), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(v, Empty(), vb, vc, Empty()), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()), s,
                  t, Empty[A, B]())
  case (Branch(v, Empty(), vb, vc, Branch(B(), ve, vf, vg, vh)), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc,
                                       Branch[A, B](B(), ve, vf, vg, vh)),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc, Empty()), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Empty[A, B]()),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc,
                Branch(B(), ve, vj, vk, vl)),
         s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Branch[A, B](B(), ve, vj, vk, vl)),
                     s, t, Empty[A, B]())
  case (Branch(v, Empty(), vf, vg, Empty()), s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Empty(), vf, vg, Branch(B(), vi, vj, vk, vl)), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg,
                                       Branch[A, B](B(), vi, vj, vk, vl)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg, Empty()), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg,
                Branch(B(), vi, vn, vo, vp)),
         s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Branch[A, B](B(), vi, vn, vo, vp)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
}

def rbt_ins[A : Orderings.ord,
             B](f: A => B => B => B, k: A, v: B, x3: rbt[A, B]):
      rbt[A, B]
  =
  (f, k, v, x3) match {
  case (f, k, v, Empty()) =>
    Branch[A, B](R(), Empty[A, B](), k, v, Empty[A, B]())
  case (f, k, v, Branch(B(), l, x, y, r)) =>
    (if (Orderings.less[A](k, x))
      balance[A, B](rbt_ins[A, B](f, k, v, l), x, y, r)
      else (if (Orderings.less[A](x, k))
             balance[A, B](l, x, y, rbt_ins[A, B](f, k, v, r))
             else Branch[A, B](B(), l, x, ((f(k))(y))(v), r)))
  case (f, k, v, Branch(R(), l, x, y, r)) =>
    (if (Orderings.less[A](k, x))
      Branch[A, B](R(), rbt_ins[A, B](f, k, v, l), x, y, r)
      else (if (Orderings.less[A](x, k))
             Branch[A, B](R(), l, x, y, rbt_ins[A, B](f, k, v, r))
             else Branch[A, B](R(), l, x, ((f(k))(y))(v), r)))
}

def rbt_insert_with_key[A : Orderings.ord,
                         B](f: A => B => B => B, k: A, v: B, t: rbt[A, B]):
      rbt[A, B]
  =
  paint[A, B](B(), rbt_ins[A, B](f, k, v, t))

def rbt_insert[A : Orderings.ord, B]: A => B => (rbt[A, B]) => rbt[A, B] =
  ((a: A) => (b: B) => (c: rbt[A, B]) =>
    rbt_insert_with_key[A, B](((_: A) => (_: B) => (nv: B) => nv), a, b, c))

def rbt_lookup[A : Orderings.ord, B](x0: rbt[A, B], k: A): Option[B] = (x0, k)
  match {
  case (Empty(), k) => None
  case (Branch(uu, l, x, y, r), k) =>
    (if (Orderings.less[A](k, x)) rbt_lookup[A, B](l, k)
      else (if (Orderings.less[A](x, k)) rbt_lookup[A, B](r, k)
             else Some[B](y)))
}

} /* object RBT_Impl */

object RBT {

abstract sealed class rbt[B, A]
final case class RBTa[B, A](a: RBT_Impl.rbt[B, A]) extends rbt[B, A]

def empty[A : Orderings.linorder, B]: rbt[A, B] =
  RBTa[A, B](RBT_Impl.Empty[A, B]())

def impl_of[B : Orderings.linorder, A](x0: rbt[B, A]): RBT_Impl.rbt[B, A] = x0
  match {
  case RBTa(x) => x
}

def insert[A : Orderings.linorder, B](xc: A, xd: B, xe: rbt[A, B]): rbt[A, B] =
  RBTa[A, B](RBT_Impl.rbt_insert[A, B].apply(xc).apply(xd).apply(impl_of[A,
                                  B](xe)))

def lookup[A : Orderings.linorder, B](x: rbt[A, B]): A => Option[B] =
  ((a: A) => RBT_Impl.rbt_lookup[A, B](impl_of[A, B](x), a))

} /* object RBT */

object Move {

abstract sealed class log_op[A, B, C]
final case class LogMove[A, B, C](a: A, b: Option[(B, C)], c: B, d: C, e: B)
  extends log_op[A, B, C]

abstract sealed class operation[A, B, C]
final case class Movea[A, B, C](a: A, b: B, c: C, d: B) extends
  operation[A, B, C]

def log_time[A, B, C](x0: log_op[A, B, C]): A = x0 match {
  case LogMove(x1, x2, x3, x4, x5) => x1
}

def move_time[A, B, C](x0: operation[A, B, C]): A = x0 match {
  case Movea(x1, x2, x3, x4) => x1
}

} /* object Move */

object Product_Type {

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

} /* object Product_Type */

object AList {

def update_with_aux[A, B : HOL.equal](v: A, k: B, f: A => A, x3: List[(B, A)]):
      List[(B, A)]
  =
  (v, k, f, x3) match {
  case (v, k, f, Nil) => List((k, f(v)))
  case (v, k, f, p :: ps) =>
    (if (HOL.eq[B](Product_Type.fst[B, A](p), k))
      (k, f(Product_Type.snd[B, A](p))) :: ps
      else p :: update_with_aux[A, B](v, k, f, ps))
}

} /* object AList */

object Foldi {

def foldli[A, B](x0: List[A], c: B => Boolean, f: A => B => B, sigma: B): B =
  (x0, c, f, sigma) match {
  case (Nil, c, f, sigma) => sigma
  case (x :: xs, c, f, sigma) =>
    (if (c(sigma)) foldli[A, B](xs, c, f, (f(x))(sigma)) else sigma)
}

} /* object Foldi */

object Lista {

def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
  case (f, a, Nil) => a
  case (f, a, x :: xs) => foldl[A, B](f, (f(a))(x), xs)
}

} /* object Lista */

object Assoc_List {

abstract sealed class assoc_list[B, A]
final case class Assoc_Lista[B, A](a: List[(B, A)]) extends assoc_list[B, A]

def empty[A, B]: assoc_list[A, B] = Assoc_Lista[A, B](Nil)

def impl_of[B, A](x0: assoc_list[B, A]): List[(B, A)] = x0 match {
  case Assoc_Lista(x) => x
}

def lookup[A : HOL.equal, B](al: assoc_list[A, B]): A => Option[B] =
  ((a: A) => Map.map_of[A, B](impl_of[A, B](al), a))

def update_with[B, A : HOL.equal](v: B, k: A, f: B => B, al: assoc_list[A, B]):
      assoc_list[A, B]
  =
  Assoc_Lista[A, B](AList.update_with_aux[B, A](v, k, f, impl_of[A, B](al)))

def update[A : HOL.equal, B](k: A, v: B): (assoc_list[A, B]) => assoc_list[A, B]
  =
  ((a: assoc_list[A, B]) => update_with[B, A](v, k, ((_: B) => v), a))

def iteratei[A, B,
              C](al: assoc_list[A, B], c: C => Boolean, f: ((A, B)) => C => C):
      C => C
  =
  ((a: C) => Foldi.foldli[(A, B), C](impl_of[A, B](al), c, f, a))

} /* object Assoc_List */

object ListMapImpl {

def iteratei_map_op_list_it_lm_ops[A, B, C](s: Assoc_List.assoc_list[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) =>
    Assoc_List.iteratei[A, B, C](s, a, b))

} /* object ListMapImpl */

object RBT_add {

def rm_iterateoi[A, B,
                  C](x0: RBT_Impl.rbt[A, B], c: C => Boolean,
                      f: ((A, B)) => C => C, sigma: C):
      C
  =
  (x0, c, f, sigma) match {
  case (RBT_Impl.Empty(), c, f, sigma) => sigma
  case (RBT_Impl.Branch(col, l, k, v, r), c, f, sigma) =>
    (if (c(sigma))
      {
        val sigmaa: C = rm_iterateoi[A, B, C](l, c, f, sigma);
        (if (c(sigmaa)) rm_iterateoi[A, B, C](r, c, f, (f((k, v)))(sigmaa))
          else sigmaa)
      }
      else sigma)
}

} /* object RBT_add */

object RBTMapImpl {

def iteratei_map_op_list_it_rm_ops[A : Orderings.linorder, B,
                                    C](s: RBT.rbt[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) => (c: C) =>
    RBT_add.rm_iterateoi[A, B, C](RBT.impl_of[A, B](s), a, b, c))

} /* object RBTMapImpl */

object HashCode {

trait hashable[A] {
  val `HashCode.hashcode`: A => Int
  val `HashCode.def_hashmap_size`: (HOL.itself[A]) => Nat.nat
}
def hashcode[A](a: A)(implicit A: hashable[A]): Int = A.`HashCode.hashcode`(a)
def def_hashmap_size[A](a: HOL.itself[A])(implicit A: hashable[A]): Nat.nat =
  A.`HashCode.def_hashmap_size`(a)
object hashable {
}

} /* object HashCode */

object Optiona {

def map_option[A, B](f: A => B, x1: Option[A]): Option[B] = (f, x1) match {
  case (f, None) => None
  case (f, Some(x2)) => Some[B](f(x2))
}

} /* object Optiona */

object HashMap_Impl {

def empty[A : HashCode.hashable, B]:
      Unit => RBT.rbt[Int, Assoc_List.assoc_list[A, B]]
  =
  ((_: Unit) => RBT.empty[Int, Assoc_List.assoc_list[A, B]])

def lookup[A : HOL.equal : HashCode.hashable,
            B](k: A, m: RBT.rbt[Int, Assoc_List.assoc_list[A, B]]):
      Option[B]
  =
  ((RBT.lookup[Int, Assoc_List.assoc_list[A,
   B]](m)).apply(HashCode.hashcode[A](k))
     match {
     case None => None
     case Some(lm) => (Assoc_List.lookup[A, B](lm)).apply(k)
   })

def update[A : HOL.equal : HashCode.hashable,
            B](k: A, v: B, m: RBT.rbt[Int, Assoc_List.assoc_list[A, B]]):
      RBT.rbt[Int, Assoc_List.assoc_list[A, B]]
  =
  {
    val hc: Int = HashCode.hashcode[A](k);
    ((RBT.lookup[Int, Assoc_List.assoc_list[A, B]](m)).apply(hc) match {
       case None =>
         RBT.insert[Int, Assoc_List.assoc_list[A,
        B]](hc, (Assoc_List.update[A, B](k, v)).apply(Assoc_List.empty[A, B]),
             m)
       case Some(bm) =>
         RBT.insert[Int, Assoc_List.assoc_list[A,
        B]](hc, (Assoc_List.update[A, B](k, v)).apply(bm), m)
     })
  }

def iteratei[A : Orderings.linorder, B, C,
              D](m: RBT.rbt[A, Assoc_List.assoc_list[B, C]], c: D => Boolean,
                  f: ((B, C)) => D => D, sigma_0: D):
      D
  =
  (RBTMapImpl.iteratei_map_op_list_it_rm_ops[A, Assoc_List.assoc_list[B, C],
      D](m)).apply(c).apply(((a: (A, Assoc_List.assoc_list[B, C])) =>
                              {
                                val (_, lm): (A, Assoc_List.assoc_list[B, C]) =
                                  a;
                                (ListMapImpl.iteratei_map_op_list_it_lm_ops[B,
                                     C, D](lm)).apply(c).apply(f)
                              })).apply(sigma_0)

} /* object HashMap_Impl */

object HashMap {

abstract sealed class hashmap[B, A]
final case class RBT_HM[B, A](a: RBT.rbt[Int, Assoc_List.assoc_list[B, A]])
  extends hashmap[B, A]

def hm_empty_const[A : HashCode.hashable, B]: hashmap[A, B] =
  RBT_HM[A, B](HashMap_Impl.empty[A, B].apply(()))

def hm_empty[A : HashCode.hashable, B]: Unit => hashmap[A, B] =
  ((_: Unit) => hm_empty_const[A, B])

def impl_of_RBT_HM[B : HashCode.hashable, A](x0: hashmap[B, A]):
      RBT.rbt[Int, Assoc_List.assoc_list[B, A]]
  =
  x0 match {
  case RBT_HM(x) => x
}

def hm_lookup[A : HOL.equal : HashCode.hashable, B](k: A, hm: hashmap[A, B]):
      Option[B]
  =
  HashMap_Impl.lookup[A, B](k, impl_of_RBT_HM[A, B](hm))

def hm_update[A : HOL.equal : HashCode.hashable,
               B](k: A, v: B, hm: hashmap[A, B]):
      hashmap[A, B]
  =
  RBT_HM[A, B](HashMap_Impl.update[A, B](k, v, impl_of_RBT_HM[A, B](hm)))

def hm_iteratei[A : HashCode.hashable, B, C](hm: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) => (c: C) =>
    HashMap_Impl.iteratei[Int, A, B, C](impl_of_RBT_HM[A, B](hm), a, b, c))

def iteratei_bmap_op_list_it_hm_basic_ops[A : HashCode.hashable, B,
   C](s: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  hm_iteratei[A, B, C](s)

def g_restrict_hm_basic_ops[A : HOL.equal : HashCode.hashable,
                             B](p: ((A, B)) => Boolean, m: hashmap[A, B]):
      hashmap[A, B]
  =
  (iteratei_bmap_op_list_it_hm_basic_ops[A, B,
  hashmap[A, B]](m)).apply(((_: hashmap[A, B]) =>
                             true)).apply(((a: (A, B)) =>
    {
      val (k, v): (A, B) = a;
      ((sigma: hashmap[A, B]) =>
        (if (p((k, v))) hm_update[A, B](k, v, sigma) else sigma))
    })).apply(hm_empty[A, B].apply(()))

} /* object HashMap */

object Move_Code {

def efficient_ancestor[A : HOL.equal : HashCode.hashable,
                        B](t: HashMap.hashmap[A, (B, A)], p: A, c: A):
      Boolean
  =
  (HashMap.hm_lookup[A, (B, A)](c, t) match {
     case None => false
     case Some(a) => {
                       val (_, aa): (B, A) = a;
                       HOL.eq[A](aa, p) || efficient_ancestor[A, B](t, p, aa)
                     }
   })

def efficient_do_op[A, B : HOL.equal : HashCode.hashable,
                     C](x0: (Move.operation[A, B, C],
                              HashMap.hashmap[B, (C, B)])):
      (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)])
  =
  x0 match {
  case (Move.Movea(t, newp, m, c), tree) =>
    (Move.LogMove[A, B,
                   C](t, Optiona.map_option[(C, B),
     (B, C)](((x: (C, B)) =>
               (Product_Type.snd[C, B](x), Product_Type.fst[C, B](x))),
              HashMap.hm_lookup[B, (C, B)](c, tree)),
                       newp, m, c),
      (if (efficient_ancestor[B, C](tree, c, newp) || HOL.eq[B](c, newp)) tree
        else HashMap.hm_update[B, (C, B)](c, (m, newp),
   HashMap.g_restrict_hm_basic_ops[B, (C,
B)](((a: (B, (C, B))) => {
                           val (ca, (_, _)): (B, (C, B)) = a;
                           ! (HOL.eq[B](c, ca))
                         }),
     tree))))
}

def efficient_redo_op[A, B : HOL.equal : HashCode.hashable,
                       C](x0: Move.log_op[A, B, C],
                           x1: (List[Move.log_op[A, B, C]],
                                 HashMap.hashmap[B, (C, B)])):
      (List[Move.log_op[A, B, C]], HashMap.hashmap[B, (C, B)])
  =
  (x0, x1) match {
  case (Move.LogMove(t, uu, p, m, c), (ops, tree)) =>
    {
      val a: (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) =
        efficient_do_op[A, B, C]((Move.Movea[A, B, C](t, p, m, c), tree))
      val (op2, aa): (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) = a;
      (op2 :: ops, aa)
    }
}

def efficient_undo_op[A, B : HOL.equal : HashCode.hashable,
                       C](x0: (Move.log_op[A, B, C],
                                HashMap.hashmap[B, (C, B)])):
      HashMap.hashmap[B, (C, B)]
  =
  x0 match {
  case (Move.LogMove(t, None, newp, m, c), tree) =>
    HashMap.g_restrict_hm_basic_ops[B, (C,
 B)](((a: (B, (C, B))) => {
                            val (ca, (_, _)): (B, (C, B)) = a;
                            ! (HOL.eq[B](ca, c))
                          }),
      tree)
  case (Move.LogMove(t, Some((oldp, oldm)), newp, m, c), tree) =>
    HashMap.hm_update[B, (C, B)](c, (oldm, oldp),
                                  HashMap.g_restrict_hm_basic_ops[B,
                           (C, B)](((a: (B, (C, B))) =>
                                     {
                                       val (ca, (_, _)): (B, (C, B)) = a;
                                       ! (HOL.eq[B](ca, c))
                                     }),
                                    tree))
}

def efficient_apply_op[A : Orderings.linorder,
                        B : HOL.equal : HashCode.hashable,
                        C](op1: Move.operation[A, B, C],
                            x1: (List[Move.log_op[A, B, C]],
                                  HashMap.hashmap[B, (C, B)])):
      (List[Move.log_op[A, B, C]], HashMap.hashmap[B, (C, B)])
  =
  (op1, x1) match {
  case (op1, (Nil, tree1)) =>
    {
      val a: (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) =
        efficient_do_op[A, B, C]((op1, tree1))
      val (op2, aa): (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) = a;
      (List(op2), aa)
    }
  case (op1, (logop :: ops, tree1)) =>
    (if (Orderings.less[A](Move.move_time[A, B, C](op1),
                            Move.log_time[A, B, C](logop)))
      efficient_redo_op[A, B,
                         C](logop,
                             efficient_apply_op[A, B,
         C](op1, (ops, efficient_undo_op[A, B, C]((logop, tree1)))))
      else {
             val a: (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) =
               efficient_do_op[A, B, C]((op1, tree1))
             val (op2, aa): (Move.log_op[A, B, C], HashMap.hashmap[B, (C, B)]) =
               a;
             (op2 :: logop :: ops, aa)
           })
}

def efficient_apply_ops[A : Orderings.linorder,
                         B : HOL.equal : HashCode.hashable,
                         C](ops: List[Move.operation[A, B, C]]):
      (List[Move.log_op[A, B, C]], HashMap.hashmap[B, (C, B)])
  =
  Lista.foldl[(List[Move.log_op[A, B, C]], HashMap.hashmap[B, (C, B)]),
               Move.operation[A, B,
                               C]](((state:
                                       (List[Move.log_op[A, B, C]],
 HashMap.hashmap[B, (C, B)]))
                                      =>
                                     (oper: Move.operation[A, B, C]) =>
                                     efficient_apply_op[A, B, C](oper, state)),
                                    (Nil, HashMap.hm_empty[B,
                    (C, B)].apply(())),
                                    ops)

} /* object Move_Code */
