(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x)
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x)
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;




structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure HOL : sig
  type 'a equal
  type 'a itself
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

datatype 'a itself = Type;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

fun map_of A_ ((l, v) :: ps) k =
  (if HOL.eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

end; (*struct Map*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder
  val ord_preorder : 'a preorder -> 'a ord
  type 'a order
  val preorder_order : 'a order -> 'a preorder
  type 'a linorder
  val order_linorder : 'a linorder -> 'a order
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

end; (*struct Orderings*)

structure RBT_Impl : sig
  type color
  datatype ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val rbt_insert : 'a Orderings.ord -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_lookup : 'a Orderings.ord -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_ins A_ f k v (Branch (B, l, x, y, r)) =
    (if Orderings.less A_ k x then balance (rbt_ins A_ f k v l) x y r
      else (if Orderings.less A_ x k then balance l x y (rbt_ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins A_ f k v (Branch (R, l, x, y, r)) =
    (if Orderings.less A_ k x then Branch (R, rbt_ins A_ f k v l, x, y, r)
      else (if Orderings.less A_ x k
             then Branch (R, l, x, y, rbt_ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun rbt_insert_with_key A_ f k v t = paint B (rbt_ins A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun rbt_lookup A_ Empty k = NONE
  | rbt_lookup A_ (Branch (uu, l, x, y, r)) k =
    (if Orderings.less A_ k x then rbt_lookup A_ l k
      else (if Orderings.less A_ x k then rbt_lookup A_ r k else SOME y));

end; (*struct RBT_Impl*)

structure RBT : sig
  type ('b, 'a) rbt
  val empty : 'a Orderings.linorder -> ('a, 'b) rbt
  val impl_of : 'b Orderings.linorder -> ('b, 'a) rbt -> ('b, 'a) RBT_Impl.rbt
  val insert : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookup : 'a Orderings.linorder -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

datatype ('b, 'a) rbt = RBT of ('b, 'a) RBT_Impl.rbt;

fun empty A_ = RBT RBT_Impl.Empty;

fun impl_of B_ (RBT x) = x;

fun insert A_ xc xd xe =
  RBT (RBT_Impl.rbt_insert
        ((Orderings.ord_preorder o Orderings.preorder_order o
           Orderings.order_linorder)
          A_)
        xc xd (impl_of A_ xe));

fun lookup A_ x =
  RBT_Impl.rbt_lookup
    ((Orderings.ord_preorder o Orderings.preorder_order o
       Orderings.order_linorder)
      A_)
    (impl_of A_ x);

end; (*struct RBT*)

structure List : sig
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
end = struct

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

end; (*struct List*)

structure Move : sig
  datatype ('a, 'b, 'c) log_op = LogMove of 'a * ('b * 'c) option * 'b * 'c * 'b
  datatype ('a, 'b, 'c) operation = Move of 'a * 'b * 'c * 'b
  val log_time : ('a, 'b, 'c) log_op -> 'a
  val move_time : ('a, 'b, 'c) operation -> 'a
end = struct

datatype ('a, 'b, 'c) log_op = LogMove of 'a * ('b * 'c) option * 'b * 'c * 'b;

datatype ('a, 'b, 'c) operation = Move of 'a * 'b * 'c * 'b;

fun log_time (LogMove (x1, x2, x3, x4, x5)) = x1;

fun move_time (Move (x1, x2, x3, x4)) = x1;

end; (*struct Move*)

structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

end; (*struct Product_Type*)

structure AList : sig
  val update_with_aux :
    'b HOL.equal -> 'a -> 'b -> ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list
end = struct

fun update_with_aux B_ v k f [] = [(k, f v)]
  | update_with_aux B_ v k f (p :: ps) =
    (if HOL.eq B_ (Product_Type.fst p) k then (k, f (Product_Type.snd p)) :: ps
      else p :: update_with_aux B_ v k f ps);

end; (*struct AList*)

structure Arith : sig
  type nat
end = struct

datatype nat = Nat of IntInf.int;

end; (*struct Arith*)

structure Foldi : sig
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

end; (*struct Foldi*)

structure Option : sig
  val map_option : ('a -> 'b) -> 'a option -> 'b option
end = struct

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

end; (*struct Option*)

structure Assoc_List : sig
  type ('b, 'a) assoc_list
  val empty : ('a, 'b) assoc_list
  val lookup : 'a HOL.equal -> ('a, 'b) assoc_list -> 'a -> 'b option
  val update :
    'a HOL.equal -> 'a -> 'b -> ('a, 'b) assoc_list -> ('a, 'b) assoc_list
  val iteratei :
    ('a, 'b) assoc_list -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

datatype ('b, 'a) assoc_list = Assoc_List of ('b * 'a) list;

val empty : ('a, 'b) assoc_list = Assoc_List [];

fun impl_of (Assoc_List x) = x;

fun lookup A_ al = Map.map_of A_ (impl_of al);

fun update_with A_ v k f al =
  Assoc_List (AList.update_with_aux A_ v k f (impl_of al));

fun update A_ k v = update_with A_ v k (fn _ => v);

fun iteratei al c f = Foldi.foldli (impl_of al) c f;

end; (*struct Assoc_List*)

structure ListMapImpl : sig
  val iteratei_map_op_list_it_lm_ops :
    ('a, 'b) Assoc_List.assoc_list ->
      ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun iteratei_map_op_list_it_lm_ops s = Assoc_List.iteratei s;

end; (*struct ListMapImpl*)

structure RBT_add : sig
  val rm_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun rm_iterateoi RBT_Impl.Empty c f sigma = sigma
  | rm_iterateoi (RBT_Impl.Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_iterateoi l c f sigma;
           in
             (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa) else sigmaa)
           end
      else sigma);

end; (*struct RBT_add*)

structure RBTMapImpl : sig
  val iteratei_map_op_list_it_rm_ops :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun iteratei_map_op_list_it_rm_ops A_ s =
  RBT_add.rm_iterateoi (RBT.impl_of A_ s);

end; (*struct RBTMapImpl*)

structure HashCode : sig
  type 'a hashable
  val hashcode : 'a hashable -> 'a -> Word32.word
  val def_hashmap_size : 'a hashable -> 'a HOL.itself -> Arith.nat
end = struct

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a HOL.itself -> Arith.nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size :
  'a hashable -> 'a HOL.itself -> Arith.nat;

end; (*struct HashCode*)

structure Uint32a : sig
  val linorder_uint32 : Word32.word Orderings.linorder
end = struct

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word Orderings.ord;

val preorder_uint32 = {ord_preorder = ord_uint32} :
  Word32.word Orderings.preorder;

val order_uint32 = {preorder_order = preorder_uint32} :
  Word32.word Orderings.order;

val linorder_uint32 = {order_linorder = order_uint32} :
  Word32.word Orderings.linorder;

end; (*struct Uint32a*)

structure HashMap_Impl : sig
  val empty :
    'a HashCode.hashable ->
      unit -> (Word32.word, ('a, 'b) Assoc_List.assoc_list) RBT.rbt
  val lookup :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> (Word32.word, ('a, 'b) Assoc_List.assoc_list) RBT.rbt -> 'b option
  val update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> (Word32.word, ('a, 'b) Assoc_List.assoc_list) RBT.rbt ->
                    (Word32.word, ('a, 'b) Assoc_List.assoc_list) RBT.rbt
  val iteratei :
    'a Orderings.linorder ->
      ('a, ('b, 'c) Assoc_List.assoc_list) RBT.rbt ->
        ('d -> bool) -> ('b * 'c -> 'd -> 'd) -> 'd -> 'd
end = struct

fun empty A_ = (fn _ => RBT.empty Uint32a.linorder_uint32);

fun lookup (A1_, A2_) k m =
  (case RBT.lookup Uint32a.linorder_uint32 m (HashCode.hashcode A2_ k)
    of NONE => NONE | SOME lm => Assoc_List.lookup A1_ lm k);

fun update (A1_, A2_) k v m =
  let
    val hc = HashCode.hashcode A2_ k;
  in
    (case RBT.lookup Uint32a.linorder_uint32 m hc
      of NONE =>
        RBT.insert Uint32a.linorder_uint32 hc
          (Assoc_List.update A1_ k v Assoc_List.empty) m
      | SOME bm =>
        RBT.insert Uint32a.linorder_uint32 hc (Assoc_List.update A1_ k v bm) m)
  end;

fun iteratei A_ m c f sigma_0 =
  RBTMapImpl.iteratei_map_op_list_it_rm_ops A_ m c
    (fn (_, lm) => ListMapImpl.iteratei_map_op_list_it_lm_ops lm c f) sigma_0;

end; (*struct HashMap_Impl*)

structure HashMap : sig
  type ('b, 'a) hashmap
  val hm_empty : 'a HashCode.hashable -> unit -> ('a, 'b) hashmap
  val hm_lookup :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val hm_update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val g_restrict_hm_basic_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a * 'b -> bool) -> ('a, 'b) hashmap -> ('a, 'b) hashmap
end = struct

datatype ('b, 'a) hashmap =
  RBT_HM of (Word32.word, ('b, 'a) Assoc_List.assoc_list) RBT.rbt;

fun hm_empty_const A_ = RBT_HM (HashMap_Impl.empty A_ ());

fun hm_empty A_ = (fn _ => hm_empty_const A_);

fun impl_of_RBT_HM B_ (RBT_HM x) = x;

fun hm_lookup (A1_, A2_) k hm =
  HashMap_Impl.lookup (A1_, A2_) k (impl_of_RBT_HM A2_ hm);

fun hm_update (A1_, A2_) k v hm =
  RBT_HM (HashMap_Impl.update (A1_, A2_) k v (impl_of_RBT_HM A2_ hm));

fun hm_iteratei A_ hm =
  HashMap_Impl.iteratei Uint32a.linorder_uint32 (impl_of_RBT_HM A_ hm);

fun iteratei_bmap_op_list_it_hm_basic_ops A_ s = hm_iteratei A_ s;

fun g_restrict_hm_basic_ops (A1_, A2_) p m =
  iteratei_bmap_op_list_it_hm_basic_ops A2_ m (fn _ => true)
    (fn (k, v) => fn sigma =>
      (if p (k, v) then hm_update (A1_, A2_) k v sigma else sigma))
    (hm_empty A2_ ());

end; (*struct HashMap*)

structure Move_Code : sig
  val efficient_ancestor :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, ('b * 'a)) HashMap.hashmap -> 'a -> 'a -> bool
  val efficient_do_op :
    'b HOL.equal * 'b HashCode.hashable ->
      ('a, 'b, 'c) Move.operation * ('b, ('c * 'b)) HashMap.hashmap ->
        ('a, 'b, 'c) Move.log_op * ('b, ('c * 'b)) HashMap.hashmap
  val efficient_redo_op :
    'b HOL.equal * 'b HashCode.hashable ->
      ('a, 'b, 'c) Move.log_op ->
        ('a, 'b, 'c) Move.log_op list * ('b, ('c * 'b)) HashMap.hashmap ->
          ('a, 'b, 'c) Move.log_op list * ('b, ('c * 'b)) HashMap.hashmap
  val efficient_undo_op :
    'b HOL.equal * 'b HashCode.hashable ->
      ('a, 'b, 'c) Move.log_op * ('b, ('c * 'b)) HashMap.hashmap ->
        ('b, ('c * 'b)) HashMap.hashmap
  val efficient_apply_op :
    'a Orderings.linorder -> 'b HOL.equal * 'b HashCode.hashable ->
      ('a, 'b, 'c) Move.operation ->
        ('a, 'b, 'c) Move.log_op list * ('b, ('c * 'b)) HashMap.hashmap ->
          ('a, 'b, 'c) Move.log_op list * ('b, ('c * 'b)) HashMap.hashmap
  val efficient_apply_ops :
    'a Orderings.linorder -> 'b HOL.equal * 'b HashCode.hashable ->
      ('a, 'b, 'c) Move.operation list ->
        ('a, 'b, 'c) Move.log_op list * ('b, ('c * 'b)) HashMap.hashmap
end = struct

fun efficient_ancestor (A1_, A2_) t p c =
  (case HashMap.hm_lookup (A1_, A2_) c t of NONE => false
    | SOME a => let
                  val (_, aa) = a;
                in
                  HOL.eq A1_ aa p orelse efficient_ancestor (A1_, A2_) t p aa
                end);

fun efficient_do_op (B1_, B2_) (Move.Move (t, newp, m, c), tree) =
  (Move.LogMove
     (t, Option.map_option (fn x => (Product_Type.snd x, Product_Type.fst x))
           (HashMap.hm_lookup (B1_, B2_) c tree),
       newp, m, c),
    (if efficient_ancestor (B1_, B2_) tree c newp orelse HOL.eq B1_ c newp
      then tree
      else HashMap.hm_update (B1_, B2_) c (m, newp)
             (HashMap.g_restrict_hm_basic_ops (B1_, B2_)
               (fn (ca, (_, _)) => not (HOL.eq B1_ c ca)) tree)));

fun efficient_redo_op (B1_, B2_) (Move.LogMove (t, uu, p, m, c)) (ops, tree) =
  let
    val a = efficient_do_op (B1_, B2_) (Move.Move (t, p, m, c), tree);
    val (op2, aa) = a;
  in
    (op2 :: ops, aa)
  end;

fun efficient_undo_op (B1_, B2_) (Move.LogMove (t, NONE, newp, m, c), tree) =
  HashMap.g_restrict_hm_basic_ops (B1_, B2_)
    (fn (ca, (_, _)) => not (HOL.eq B1_ ca c)) tree
  | efficient_undo_op (B1_, B2_)
    (Move.LogMove (t, SOME (oldp, oldm), newp, m, c), tree) =
    HashMap.hm_update (B1_, B2_) c (oldm, oldp)
      (HashMap.g_restrict_hm_basic_ops (B1_, B2_)
        (fn (ca, (_, _)) => not (HOL.eq B1_ ca c)) tree);

fun efficient_apply_op A_ (B1_, B2_) op1 ([], tree1) =
  let
    val a = efficient_do_op (B1_, B2_) (op1, tree1);
    val (op2, aa) = a;
  in
    ([op2], aa)
  end
  | efficient_apply_op A_ (B1_, B2_) op1 (logop :: ops, tree1) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A_)
          (Move.move_time op1) (Move.log_time logop)
      then efficient_redo_op (B1_, B2_) logop
             (efficient_apply_op A_ (B1_, B2_) op1
               (ops, efficient_undo_op (B1_, B2_) (logop, tree1)))
      else let
             val a = efficient_do_op (B1_, B2_) (op1, tree1);
             val (op2, aa) = a;
           in
             (op2 :: logop :: ops, aa)
           end);

fun efficient_apply_ops A_ (B1_, B2_) ops =
  List.foldl
    (fn state => fn oper => efficient_apply_op A_ (B1_, B2_) oper state)
    ([], HashMap.hm_empty B2_ ()) ops;

end; (*struct Move_Code*)
