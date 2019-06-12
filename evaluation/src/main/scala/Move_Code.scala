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

object generated {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def integer_of_int(x0: int): BigInt = x0 match {
  case int_of_integer(k) => k
}

def less_eq_int(k: int, l: int): Boolean =
  integer_of_int(k) <= integer_of_int(l)

trait ord[A] {
  val `generated.less_eq`: (A, A) => Boolean
  val `generated.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`generated.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`generated.less`(a, b)
object ord {
  implicit def `generated.ord_integer`: ord[BigInt] = new ord[BigInt] {
    val `generated.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `generated.less` = (a: BigInt, b: BigInt) => a < b
  }
  implicit def `generated.ord_prod`[A : ord, B : ord]: ord[(A, B)] = new
    ord[(A, B)] {
    val `generated.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
    val `generated.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
  }
  implicit def `generated.ord_literal`: ord[String] = new ord[String] {
    val `generated.less_eq` = (a: String, b: String) => a <= b
    val `generated.less` = (a: String, b: String) => a < b
  }
  implicit def `generated.ord_uint32`: ord[Int] = new ord[Int] {
    val `generated.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `generated.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
  implicit def `generated.ord_int`: ord[int] = new ord[int] {
    val `generated.less_eq` = (a: int, b: int) => less_eq_int(a, b)
    val `generated.less` = (a: int, b: int) => less_int(a, b)
  }
}

def less_int(k: int, l: int): Boolean = integer_of_int(k) < integer_of_int(l)

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def
    `generated.preorder_prod`[A : preorder, B : preorder]: preorder[(A, B)] =
    new preorder[(A, B)] {
    val `generated.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
    val `generated.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
  }
  implicit def `generated.preorder_literal`: preorder[String] = new
    preorder[String] {
    val `generated.less_eq` = (a: String, b: String) => a <= b
    val `generated.less` = (a: String, b: String) => a < b
  }
  implicit def `generated.preorder_uint32`: preorder[Int] = new preorder[Int] {
    val `generated.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `generated.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
  implicit def `generated.preorder_int`: preorder[int] = new preorder[int] {
    val `generated.less_eq` = (a: int, b: int) => less_eq_int(a, b)
    val `generated.less` = (a: int, b: int) => less_int(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `generated.order_prod`[A : order, B : order]: order[(A, B)] = new
    order[(A, B)] {
    val `generated.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
    val `generated.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
  }
  implicit def `generated.order_literal`: order[String] = new order[String] {
    val `generated.less_eq` = (a: String, b: String) => a <= b
    val `generated.less` = (a: String, b: String) => a < b
  }
  implicit def `generated.order_uint32`: order[Int] = new order[Int] {
    val `generated.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `generated.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
  implicit def `generated.order_int`: order[int] = new order[int] {
    val `generated.less_eq` = (a: int, b: int) => less_eq_int(a, b)
    val `generated.less` = (a: int, b: int) => less_int(a, b)
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def
    `generated.linorder_prod`[A : linorder, B : linorder]: linorder[(A, B)] =
    new linorder[(A, B)] {
    val `generated.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
    val `generated.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
  }
  implicit def `generated.linorder_literal`: linorder[String] = new
    linorder[String] {
    val `generated.less_eq` = (a: String, b: String) => a <= b
    val `generated.less` = (a: String, b: String) => a < b
  }
  implicit def `generated.linorder_uint32`: linorder[Int] = new linorder[Int] {
    val `generated.less_eq` = (a: Int, b: Int) => Uint32.less_eq(a, b)
    val `generated.less` = (a: Int, b: Int) => Uint32.less(a, b)
  }
  implicit def `generated.linorder_int`: linorder[int] = new linorder[int] {
    val `generated.less_eq` = (a: int, b: int) => less_eq_int(a, b)
    val `generated.less` = (a: int, b: int) => less_int(a, b)
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

abstract sealed class char
final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
        g: Boolean, h: Boolean)
  extends char

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def def_hashmap_size_char: (itself[char]) => nat =
  ((_: itself[char]) => nat_of_integer(BigInt(32)))

trait zero[A] {
  val `generated.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`generated.zero`
object zero {
  implicit def `generated.zero_integer`: zero[BigInt] = new zero[BigInt] {
    val `generated.zero` = BigInt(0)
  }
}

trait one[A] {
  val `generated.one`: A
}
def one[A](implicit A: one[A]): A = A.`generated.one`
object one {
  implicit def `generated.one_integer`: one[BigInt] = new one[BigInt] {
    val `generated.one` = one_integera
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def `generated.zero_neq_one_integer`: zero_neq_one[BigInt] = new
    zero_neq_one[BigInt] {
    val `generated.zero` = BigInt(0)
    val `generated.one` = one_integera
  }
}

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => one[A]
  case false => zero[A]
}

def one_integera: BigInt = BigInt(1)

def integer_of_char(x0: char): BigInt = x0 match {
  case Char(b0, b1, b2, b3, b4, b5, b6, b7) =>
    ((((((of_bool[BigInt](b7) * BigInt(2) + of_bool[BigInt](b6)) * BigInt(2) +
          of_bool[BigInt](b5)) *
          BigInt(2) +
         of_bool[BigInt](b4)) *
         BigInt(2) +
        of_bool[BigInt](b3)) *
        BigInt(2) +
       of_bool[BigInt](b2)) *
       BigInt(2) +
      of_bool[BigInt](b1)) *
      BigInt(2) +
      of_bool[BigInt](b0)
}

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def int_of_char: char => int =
  comp[BigInt, int,
        char](((a: BigInt) => int_of_integer(a)),
               ((a: char) => integer_of_char(a)))

def uint32_of_int(i: int): Int = (integer_of_int(i)).intValue

def hashcode_char(c: char): Int = uint32_of_int(int_of_char.apply(c))

trait hashable[A] {
  val `generated.hashcode`: A => Int
  val `generated.def_hashmap_size`: (itself[A]) => nat
}
def hashcode[A](a: A)(implicit A: hashable[A]): Int = A.`generated.hashcode`(a)
def def_hashmap_size[A](a: itself[A])(implicit A: hashable[A]): nat =
  A.`generated.def_hashmap_size`(a)
object hashable {
  implicit def `generated.hashable_literal`: hashable[String] = new
    hashable[String] {
    val `generated.hashcode` = (a: String) => hashcode_literal(a)
    val `generated.def_hashmap_size` = (a: itself[String]) =>
      def_hashmap_size_literal(a)
  }
  implicit def `generated.hashable_char`: hashable[char] = new hashable[char] {
    val `generated.hashcode` = (a: char) => hashcode_char(a)
    val `generated.def_hashmap_size` = (a: itself[char]) =>
      def_hashmap_size_char.apply(a)
  }
}

trait equal[A] {
  val `generated.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`generated.equal`(a, b)
object equal {
  implicit def `generated.equal_literal`: equal[String] = new equal[String] {
    val `generated.equal` = (a: String, b: String) => a == b
  }
}

def def_hashmap_size_literal(uu: itself[String]): nat =
  nat_of_integer(BigInt(10))

def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
  case (f, a, Nil) => a
  case (f, a, x :: xs) => foldl[A, B](f, (f(a))(x), xs)
}

def hashcode_list[A : hashable]: (List[A]) => Int =
  ((a: List[A]) =>
    foldl[Int, A](((h: Int) => (x: A) =>
                    h * BigInt(33).intValue + hashcode[A](x)),
                   BigInt(5381).intValue, a))

def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s): (BigInt, BigInt) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })

def char_of_integer(k: BigInt): char =
  {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    Char(b0, b1, b2, b3, b4, b5, b6, aa)
  }

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def explode(s: String): List[char] =
  map[BigInt,
       char](((a: BigInt) => char_of_integer(a)),
              (s.toList.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })))

def hashcode_literal(s: String): Int = hashcode_list[char].apply(explode(s))

def less_eq_prod[A : ord, B : ord](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((x1, y1), (x2, y2)) =>
    less[A](x1, x2) || less_eq[A](x1, x2) && less_eq[B](y1, y2)
}

def less_prod[A : ord, B : ord](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((x1, y1), (x2, y2)) =>
    less[A](x1, x2) || less_eq[A](x1, x2) && less[B](y1, y2)
}

abstract sealed class color
final case class R() extends color
final case class B() extends color

abstract sealed class rbta[A, B]
final case class Empty[A, B]() extends rbta[A, B]
final case class
  Branch[A, B](a: color, b: rbta[A, B], c: A, d: B, e: rbta[A, B])
  extends rbta[A, B]

abstract sealed class rbt[B, A]
final case class RBT[B, A](a: rbta[B, A]) extends rbt[B, A]

abstract sealed class log_op[A, B, C]
final case class LogMove[A, B, C](a: A, b: Option[(B, C)], c: B, d: C, e: B)
  extends log_op[A, B, C]

abstract sealed class operation[A, B, C]
final case class Move[A, B, C](a: A, b: B, c: C, d: B) extends
  operation[A, B, C]

abstract sealed class assoc_list[B, A]
final case class Assoc_List[B, A](a: List[(B, A)]) extends assoc_list[B, A]

abstract sealed class hashmap[B, A]
final case class RBT_HM[B, A](a: rbt[Int, assoc_list[B, A]]) extends
  hashmap[B, A]

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def empty[A : linorder, B]: rbt[A, B] = RBT[A, B](Empty[A, B]())

def map_of[A : equal, B](x0: List[(A, B)], k: A): Option[B] = (x0, k) match {
  case ((l, v) :: ps, k) =>
    (if (eq[A](l, k)) Some[B](v) else map_of[A, B](ps, k))
  case (Nil, k) => None
}

def balance[A, B](x0: rbta[A, B], s: A, t: B, x3: rbta[A, B]): rbta[A, B] =
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

def rbt_ins[A : ord, B](f: A => B => B => B, k: A, v: B, x3: rbta[A, B]):
      rbta[A, B]
  =
  (f, k, v, x3) match {
  case (f, k, v, Empty()) =>
    Branch[A, B](R(), Empty[A, B](), k, v, Empty[A, B]())
  case (f, k, v, Branch(B(), l, x, y, r)) =>
    (if (less[A](k, x)) balance[A, B](rbt_ins[A, B](f, k, v, l), x, y, r)
      else (if (less[A](x, k)) balance[A, B](l, x, y, rbt_ins[A, B](f, k, v, r))
             else Branch[A, B](B(), l, x, ((f(k))(y))(v), r)))
  case (f, k, v, Branch(R(), l, x, y, r)) =>
    (if (less[A](k, x)) Branch[A, B](R(), rbt_ins[A, B](f, k, v, l), x, y, r)
      else (if (less[A](x, k))
             Branch[A, B](R(), l, x, y, rbt_ins[A, B](f, k, v, r))
             else Branch[A, B](R(), l, x, ((f(k))(y))(v), r)))
}

def paint[A, B](c: color, x1: rbta[A, B]): rbta[A, B] = (c, x1) match {
  case (c, Empty()) => Empty[A, B]()
  case (c, Branch(uu, l, k, v, r)) => Branch[A, B](c, l, k, v, r)
}

def rbt_insert_with_key[A : ord,
                         B](f: A => B => B => B, k: A, v: B, t: rbta[A, B]):
      rbta[A, B]
  =
  paint[A, B](B(), rbt_ins[A, B](f, k, v, t))

def rbt_insert[A : ord, B]: A => B => (rbta[A, B]) => rbta[A, B] =
  ((a: A) => (b: B) => (c: rbta[A, B]) =>
    rbt_insert_with_key[A, B](((_: A) => (_: B) => (nv: B) => nv), a, b, c))

def impl_of[B : linorder, A](x0: rbt[B, A]): rbta[B, A] = x0 match {
  case RBT(x) => x
}

def insert[A : linorder, B](xc: A, xd: B, xe: rbt[A, B]): rbt[A, B] =
  RBT[A, B](rbt_insert[A, B].apply(xc).apply(xd).apply(impl_of[A, B](xe)))

def rbt_lookup[A : ord, B](x0: rbta[A, B], k: A): Option[B] = (x0, k) match {
  case (Empty(), k) => None
  case (Branch(uu, l, x, y, r), k) =>
    (if (less[A](k, x)) rbt_lookup[A, B](l, k)
      else (if (less[A](x, k)) rbt_lookup[A, B](r, k) else Some[B](y)))
}

def lookup[A : linorder, B](x: rbt[A, B]): A => Option[B] =
  ((a: A) => rbt_lookup[A, B](impl_of[A, B](x), a))

def foldli[A, B](x0: List[A], c: B => Boolean, f: A => B => B, sigma: B): B =
  (x0, c, f, sigma) match {
  case (Nil, c, f, sigma) => sigma
  case (x :: xs, c, f, sigma) =>
    (if (c(sigma)) foldli[A, B](xs, c, f, (f(x))(sigma)) else sigma)
}

def emptya[A, B]: assoc_list[A, B] = Assoc_List[A, B](Nil)

def emptyb[A : hashable, B]: Unit => rbt[Int, assoc_list[A, B]] =
  ((_: Unit) => empty[Int, assoc_list[A, B]])

def hm_empty_const[A : hashable, B]: hashmap[A, B] =
  RBT_HM[A, B](emptyb[A, B].apply(()))

def hm_empty[A : hashable, B]: Unit => hashmap[A, B] =
  ((_: Unit) => hm_empty_const[A, B])

def impl_ofa[B, A](x0: assoc_list[B, A]): List[(B, A)] = x0 match {
  case Assoc_List(x) => x
}

def lookupa[A : equal, B](al: assoc_list[A, B]): A => Option[B] =
  ((a: A) => map_of[A, B](impl_ofa[A, B](al), a))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def update_with_aux[A, B : equal](v: A, k: B, f: A => A, x3: List[(B, A)]):
      List[(B, A)]
  =
  (v, k, f, x3) match {
  case (v, k, f, Nil) => List((k, f(v)))
  case (v, k, f, p :: ps) =>
    (if (eq[B](fst[B, A](p), k)) (k, f(snd[B, A](p))) :: ps
      else p :: update_with_aux[A, B](v, k, f, ps))
}

def update_with[B, A : equal](v: B, k: A, f: B => B, al: assoc_list[A, B]):
      assoc_list[A, B]
  =
  Assoc_List[A, B](update_with_aux[B, A](v, k, f, impl_ofa[A, B](al)))

def update[A : equal, B](k: A, v: B): (assoc_list[A, B]) => assoc_list[A, B] =
  ((a: assoc_list[A, B]) => update_with[B, A](v, k, ((_: B) => v), a))

def impl_of_RBT_HM[B : hashable, A](x0: hashmap[B, A]):
      rbt[Int, assoc_list[B, A]]
  =
  x0 match {
  case RBT_HM(x) => x
}

def lookupb[A : equal : hashable, B](k: A, m: rbt[Int, assoc_list[A, B]]):
      Option[B]
  =
  ((lookup[Int, assoc_list[A, B]](m)).apply(hashcode[A](k)) match {
     case None => None
     case Some(lm) => (lookupa[A, B](lm)).apply(k)
   })

def hm_lookup[A : equal : hashable, B](k: A, hm: hashmap[A, B]): Option[B] =
  lookupb[A, B](k, impl_of_RBT_HM[A, B](hm))

def updatea[A : equal : hashable, B](k: A, v: B, m: rbt[Int, assoc_list[A, B]]):
      rbt[Int, assoc_list[A, B]]
  =
  {
    val hc: Int = hashcode[A](k);
    ((lookup[Int, assoc_list[A, B]](m)).apply(hc) match {
       case None =>
         insert[Int, assoc_list[A, B]](hc,
(update[A, B](k, v)).apply(emptya[A, B]), m)
       case Some(bm) =>
         insert[Int, assoc_list[A, B]](hc, (update[A, B](k, v)).apply(bm), m)
     })
  }

def hm_update[A : equal : hashable, B](k: A, v: B, hm: hashmap[A, B]):
      hashmap[A, B]
  =
  RBT_HM[A, B](updatea[A, B](k, v, impl_of_RBT_HM[A, B](hm)))

def iteratei[A, B,
              C](al: assoc_list[A, B], c: C => Boolean, f: ((A, B)) => C => C):
      C => C
  =
  ((a: C) => foldli[(A, B), C](impl_ofa[A, B](al), c, f, a))

def iteratei_map_op_list_it_lm_ops[A, B, C](s: assoc_list[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) => iteratei[A, B, C](s, a, b))

def rm_iterateoi[A, B,
                  C](x0: rbta[A, B], c: C => Boolean, f: ((A, B)) => C => C,
                      sigma: C):
      C
  =
  (x0, c, f, sigma) match {
  case (Empty(), c, f, sigma) => sigma
  case (Branch(col, l, k, v, r), c, f, sigma) =>
    (if (c(sigma))
      {
        val sigmaa: C = rm_iterateoi[A, B, C](l, c, f, sigma);
        (if (c(sigmaa)) rm_iterateoi[A, B, C](r, c, f, (f((k, v)))(sigmaa))
          else sigmaa)
      }
      else sigma)
}

def iteratei_map_op_list_it_rm_ops[A : linorder, B, C](s: rbt[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) => (c: C) =>
    rm_iterateoi[A, B, C](impl_of[A, B](s), a, b, c))

def iterateia[A : linorder, B, C,
               D](m: rbt[A, assoc_list[B, C]], c: D => Boolean,
                   f: ((B, C)) => D => D, sigma_0: D):
      D
  =
  (iteratei_map_op_list_it_rm_ops[A, assoc_list[B, C],
                                   D](m)).apply(c).apply(((a:
                     (A, assoc_list[B, C]))
                    =>
                   {
                     val (_, lm): (A, assoc_list[B, C]) = a;
                     (iteratei_map_op_list_it_lm_ops[B, C,
              D](lm)).apply(c).apply(f)
                   })).apply(sigma_0)

def hm_iteratei[A : hashable, B, C](hm: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ((a: C => Boolean) => (b: ((A, B)) => C => C) => (c: C) =>
    iterateia[Int, A, B, C](impl_of_RBT_HM[A, B](hm), a, b, c))

def log_time[A, B, C](x0: log_op[A, B, C]): A = x0 match {
  case LogMove(x1, x2, x3, x4, x5) => x1
}

def move_time[A, B, C](x0: operation[A, B, C]): A = x0 match {
  case Move(x1, x2, x3, x4) => x1
}

def map_option[A, B](f: A => B, x1: Option[A]): Option[B] = (f, x1) match {
  case (f, None) => None
  case (f, Some(x2)) => Some[B](f(x2))
}

def iteratei_bmap_op_list_it_hm_basic_ops[A : hashable, B, C](s: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  hm_iteratei[A, B, C](s)

def g_restrict_hm_basic_ops[A : equal : hashable,
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

def efficient_ancestor[A : equal : hashable,
                        B](t: hashmap[A, (B, A)], p: A, c: A):
      Boolean
  =
  (hm_lookup[A, (B, A)](c, t) match {
     case None => false
     case Some(a) => {
                       val (_, aa): (B, A) = a;
                       eq[A](aa, p) || efficient_ancestor[A, B](t, p, aa)
                     }
   })

def efficient_do_op[A, B : equal : hashable,
                     C](x0: (operation[A, B, C], hashmap[B, (C, B)])):
      (log_op[A, B, C], hashmap[B, (C, B)])
  =
  x0 match {
  case (Move(t, newp, m, c), tree) =>
    (LogMove[A, B,
              C](t, map_option[(C, B),
                                (B, C)](((x: (C, B)) =>
  (snd[C, B](x), fst[C, B](x))),
 hm_lookup[B, (C, B)](c, tree)),
                  newp, m, c),
      (if (efficient_ancestor[B, C](tree, c, newp) || eq[B](c, newp)) tree
        else hm_update[B, (C, B)](c, (m, newp),
                                   g_restrict_hm_basic_ops[B,
                    (C, B)](((a: (B, (C, B))) =>
                              {
                                val (ca, (_, _)): (B, (C, B)) = a;
                                ! (eq[B](c, ca))
                              }),
                             tree))))
}

def efficient_undo_op[A, B : equal : hashable,
                       C](x0: (log_op[A, B, C], hashmap[B, (C, B)])):
      hashmap[B, (C, B)]
  =
  x0 match {
  case (LogMove(t, None, newp, m, c), tree) =>
    g_restrict_hm_basic_ops[B, (C, B)](((a: (B, (C, B))) =>
 {
   val (ca, (_, _)): (B, (C, B)) = a;
   ! (eq[B](ca, c))
 }),
tree)
  case (LogMove(t, Some((oldp, oldm)), newp, m, c), tree) =>
    hm_update[B, (C, B)](c, (oldm, oldp),
                          g_restrict_hm_basic_ops[B,
           (C, B)](((a: (B, (C, B))) => {
  val (ca, (_, _)): (B, (C, B)) = a;
  ! (eq[B](ca, c))
}),
                    tree))
}

def efficient_redo_op[A, B : equal : hashable,
                       C](x0: log_op[A, B, C],
                           x1: (List[log_op[A, B, C]], hashmap[B, (C, B)])):
      (List[log_op[A, B, C]], hashmap[B, (C, B)])
  =
  (x0, x1) match {
  case (LogMove(t, uu, p, m, c), (ops, tree)) =>
    {
      val a: (log_op[A, B, C], hashmap[B, (C, B)]) =
        efficient_do_op[A, B, C]((Move[A, B, C](t, p, m, c), tree))
      val (op2, aa): (log_op[A, B, C], hashmap[B, (C, B)]) = a;
      (op2 :: ops, aa)
    }
}

def efficient_apply_op[A : linorder, B : equal : hashable,
                        C](op1: operation[A, B, C],
                            x1: (List[log_op[A, B, C]], hashmap[B, (C, B)])):
      (List[log_op[A, B, C]], hashmap[B, (C, B)])
  =
  (op1, x1) match {
  case (op1, (Nil, tree1)) =>
    {
      val a: (log_op[A, B, C], hashmap[B, (C, B)]) =
        efficient_do_op[A, B, C]((op1, tree1))
      val (op2, aa): (log_op[A, B, C], hashmap[B, (C, B)]) = a;
      (List(op2), aa)
    }
  case (op1, (logop :: ops, tree1)) =>
    (if (less[A](move_time[A, B, C](op1), log_time[A, B, C](logop)))
      efficient_redo_op[A, B,
                         C](logop,
                             efficient_apply_op[A, B,
         C](op1, (ops, efficient_undo_op[A, B, C]((logop, tree1)))))
      else {
             val a: (log_op[A, B, C], hashmap[B, (C, B)]) =
               efficient_do_op[A, B, C]((op1, tree1))
             val (op2, aa): (log_op[A, B, C], hashmap[B, (C, B)]) = a;
             (op2 :: logop :: ops, aa)
           })
}

def example_apply_op:
      (operation[(int, String), String, String]) =>
        ((List[log_op[(int, String), String, String]],
          hashmap[String, (String, String)])) =>
          (List[log_op[(int, String), String, String]],
            hashmap[String, (String, String)])
  =
  ((a: operation[(int, String), String, String]) =>
    (b: (List[log_op[(int, String), String, String]],
          hashmap[String, (String, String)]))
      =>
    efficient_apply_op[(int, String), String, String](a, b))

} /* object generated */
