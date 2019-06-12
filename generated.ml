module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Big_int.big_int -> bool -> int32
  val shiftl : int32 -> Big_int.big_int -> int32
  val shiftr : int32 -> Big_int.big_int -> int32
  val shiftr_signed : int32 -> Big_int.big_int -> int32
  val test_bit : int32 -> Big_int.big_int -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Big_int.int_of_big_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Big_int.int_of_big_int n);;

let shiftr x n = Int32.shift_right_logical x (Big_int.int_of_big_int n);;

let shiftr_signed x n = Int32.shift_right x (Big_int.int_of_big_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Big_int.int_of_big_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Bits_Integer : sig
  val and_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val or_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftl : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftr : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val test_bit : Big_int.big_int -> Big_int.big_int -> bool
end = struct

let and_pninteger bi1 bi2 =
  Big_int.and_big_int bi1
    (Big_int.xor_big_int
      (Big_int.pred_big_int
        (Big_int.shift_left_big_int Big_int.unit_big_int
           (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
      (Big_int.pred_big_int (Big_int.minus_big_int bi2)));;

let or_pninteger bi1 bi2 =
  Big_int.pred_big_int (Big_int.minus_big_int
    (Big_int.and_big_int
      (Big_int.xor_big_int
         (Big_int.pred_big_int
           (Big_int.shift_left_big_int Big_int.unit_big_int
              (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                   (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
         bi1)
      (Big_int.pred_big_int (Big_int.minus_big_int bi2))));;

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Big_int.shift_left_big_int x (Big_int.int_of_big_int n);;

let shiftr x n = Big_int.shift_right_big_int x (Big_int.int_of_big_int n);;

let test_bit x n = 
  Big_int.eq_big_int 
    (Big_int.extract_big_int x (Big_int.int_of_big_int n) 1) 
    Big_int.unit_big_int

end;; (*struct Bits_Integer*)

module HOL : sig
  type 'a equal
  type 'a itself
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

type 'a itself = Type;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if HOL.eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

end;; (*struct Map*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

end;; (*struct Orderings*)

module RBT_Impl : sig
  type color
  type ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val rbt_insert : 'a Orderings.ord -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_lookup : 'a Orderings.ord -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if Orderings.less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if Orderings.less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if Orderings.less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if Orderings.less _A x k
                 then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if Orderings.less _A k x then rbt_lookup _A l k
          else (if Orderings.less _A x k then rbt_lookup _A r k else Some y));;

end;; (*struct RBT_Impl*)

module RBT : sig
  type ('b, 'a) rbt
  val empty : 'a Orderings.linorder -> ('a, 'b) rbt
  val impl_of : 'b Orderings.linorder -> ('b, 'a) rbt -> ('b, 'a) RBT_Impl.rbt
  val insert : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookup : 'a Orderings.linorder -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

type ('b, 'a) rbt = RBT of ('b, 'a) RBT_Impl.rbt;;

let rec empty _A = RBT RBT_Impl.Empty;;

let rec impl_of _B (RBT x) = x;;

let rec insert _A
  xc xd xe =
    RBT (RBT_Impl.rbt_insert
          _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
          xc xd (impl_of _A xe));;

let rec lookup _A
  x = RBT_Impl.rbt_lookup
        _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
        (impl_of _A x);;

end;; (*struct RBT*)

module Move : sig
  type ('a, 'b, 'c) log_op = LogMove of 'a * ('b * 'c) option * 'b * 'c * 'b
  type ('a, 'b, 'c) operation = Move of 'a * 'b * 'c * 'b
  val log_time : ('a, 'b, 'c) log_op -> 'a
  val move_time : ('a, 'b, 'c) operation -> 'a
end = struct

type ('a, 'b, 'c) log_op = LogMove of 'a * ('b * 'c) option * 'b * 'c * 'b;;

type ('a, 'b, 'c) operation = Move of 'a * 'b * 'c * 'b;;

let rec log_time (LogMove (x1, x2, x3, x4, x5)) = x1;;

let rec move_time (Move (x1, x2, x3, x4)) = x1;;

end;; (*struct Move*)

module Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

end;; (*struct Product_Type*)

module AList : sig
  val update_with_aux :
    'b HOL.equal -> 'a -> 'b -> ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list
end = struct

let rec update_with_aux _B
  v k f x3 = match v, k, f, x3 with v, k, f, [] -> [(k, f v)]
    | v, k, f, p :: ps ->
        (if HOL.eq _B (Product_Type.fst p) k
          then (k, f (Product_Type.snd p)) :: ps
          else p :: update_with_aux _B v k f ps);;

end;; (*struct AList*)

module Arith : sig
  type nat
end = struct

type nat = Nat of Big_int.big_int;;

end;; (*struct Arith*)

module Foldi : sig
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

let rec foldli
  x0 c f sigma = match x0, c, f, sigma with [], c, f, sigma -> sigma
    | x :: xs, c, f, sigma ->
        (if c sigma then foldli xs c f (f x sigma) else sigma);;

end;; (*struct Foldi*)

module Lista : sig
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
end = struct

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

end;; (*struct Lista*)

module Option : sig
  val map_option : ('a -> 'b) -> 'a option -> 'b option
end = struct

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

end;; (*struct Option*)

module Assoc_List : sig
  type ('b, 'a) assoc_list
  val empty : ('a, 'b) assoc_list
  val lookup : 'a HOL.equal -> ('a, 'b) assoc_list -> 'a -> 'b option
  val update :
    'a HOL.equal -> 'a -> 'b -> ('a, 'b) assoc_list -> ('a, 'b) assoc_list
  val iteratei :
    ('a, 'b) assoc_list -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

type ('b, 'a) assoc_list = Assoc_List of ('b * 'a) list;;

let empty : ('a, 'b) assoc_list = Assoc_List [];;

let rec impl_of (Assoc_List x) = x;;

let rec lookup _A al = Map.map_of _A (impl_of al);;

let rec update_with _A
  v k f al = Assoc_List (AList.update_with_aux _A v k f (impl_of al));;

let rec update _A k v = update_with _A v k (fun _ -> v);;

let rec iteratei al c f = Foldi.foldli (impl_of al) c f;;

end;; (*struct Assoc_List*)

module ListMapImpl : sig
  val iteratei_map_op_list_it_lm_ops :
    ('a, 'b) Assoc_List.assoc_list ->
      ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec iteratei_map_op_list_it_lm_ops s = Assoc_List.iteratei s;;

end;; (*struct ListMapImpl*)

module RBT_add : sig
  val rm_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec rm_iterateoi
  x0 c f sigma = match x0, c, f, sigma with RBT_Impl.Empty, c, f, sigma -> sigma
    | RBT_Impl.Branch (col, l, k, v, r), c, f, sigma ->
        (if c sigma
          then (let sigmaa = rm_iterateoi l c f sigma in
                 (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa)
                   else sigmaa))
          else sigma);;

end;; (*struct RBT_add*)

module RBTMapImpl : sig
  val iteratei_map_op_list_it_rm_ops :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec iteratei_map_op_list_it_rm_ops _A
  s = RBT_add.rm_iterateoi (RBT.impl_of _A s);;

end;; (*struct RBTMapImpl*)

module HashCode : sig
  type 'a hashable =
    {hashcode : 'a -> int32; def_hashmap_size : 'a HOL.itself -> Arith.nat}
  val hashcode : 'a hashable -> 'a -> int32
  val def_hashmap_size : 'a hashable -> 'a HOL.itself -> Arith.nat
end = struct

type 'a hashable =
  {hashcode : 'a -> int32; def_hashmap_size : 'a HOL.itself -> Arith.nat};;
let hashcode _A = _A.hashcode;;
let def_hashmap_size _A = _A.def_hashmap_size;;

end;; (*struct HashCode*)

module Uint32a : sig
  val linorder_uint32 : int32 Orderings.linorder
end = struct

let ord_uint32 =
  ({Orderings.less_eq = Uint32.less_eq; Orderings.less = Uint32.less} :
    int32 Orderings.ord);;

let preorder_uint32 =
  ({Orderings.ord_preorder = ord_uint32} : int32 Orderings.preorder);;

let order_uint32 =
  ({Orderings.preorder_order = preorder_uint32} : int32 Orderings.order);;

let linorder_uint32 =
  ({Orderings.order_linorder = order_uint32} : int32 Orderings.linorder);;

end;; (*struct Uint32a*)

module HashMap_Impl : sig
  val empty :
    'a HashCode.hashable ->
      unit -> (int32, ('a, 'b) Assoc_List.assoc_list) RBT.rbt
  val lookup :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> (int32, ('a, 'b) Assoc_List.assoc_list) RBT.rbt -> 'b option
  val update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> (int32, ('a, 'b) Assoc_List.assoc_list) RBT.rbt ->
                    (int32, ('a, 'b) Assoc_List.assoc_list) RBT.rbt
  val iteratei :
    'a Orderings.linorder ->
      ('a, ('b, 'c) Assoc_List.assoc_list) RBT.rbt ->
        ('d -> bool) -> ('b * 'c -> 'd -> 'd) -> 'd -> 'd
end = struct

let rec empty _A = (fun _ -> RBT.empty Uint32a.linorder_uint32);;

let rec lookup (_A1, _A2)
  k m = (match RBT.lookup Uint32a.linorder_uint32 m (HashCode.hashcode _A2 k)
          with None -> None | Some lm -> Assoc_List.lookup _A1 lm k);;

let rec update (_A1, _A2)
  k v m =
    (let hc = HashCode.hashcode _A2 k in
      (match RBT.lookup Uint32a.linorder_uint32 m hc
        with None ->
          RBT.insert Uint32a.linorder_uint32 hc
            (Assoc_List.update _A1 k v Assoc_List.empty) m
        | Some bm ->
          RBT.insert Uint32a.linorder_uint32 hc (Assoc_List.update _A1 k v bm)
            m));;

let rec iteratei _A
  m c f sigma_0 =
    RBTMapImpl.iteratei_map_op_list_it_rm_ops _A m c
      (fun (_, lm) -> ListMapImpl.iteratei_map_op_list_it_lm_ops lm c f)
      sigma_0;;

end;; (*struct HashMap_Impl*)

module HashMap : sig
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

type ('b, 'a) hashmap =
  RBT_HM of (int32, ('b, 'a) Assoc_List.assoc_list) RBT.rbt;;

let rec hm_empty_const _A = RBT_HM (HashMap_Impl.empty _A ());;

let rec hm_empty _A = (fun _ -> hm_empty_const _A);;

let rec impl_of_RBT_HM _B (RBT_HM x) = x;;

let rec hm_lookup (_A1, _A2)
  k hm = HashMap_Impl.lookup (_A1, _A2) k (impl_of_RBT_HM _A2 hm);;

let rec hm_update (_A1, _A2)
  k v hm = RBT_HM (HashMap_Impl.update (_A1, _A2) k v (impl_of_RBT_HM _A2 hm));;

let rec hm_iteratei _A
  hm = HashMap_Impl.iteratei Uint32a.linorder_uint32 (impl_of_RBT_HM _A hm);;

let rec iteratei_bmap_op_list_it_hm_basic_ops _A s = hm_iteratei _A s;;

let rec g_restrict_hm_basic_ops (_A1, _A2)
  p m = iteratei_bmap_op_list_it_hm_basic_ops _A2 m (fun _ -> true)
          (fun (k, v) sigma ->
            (if p (k, v) then hm_update (_A1, _A2) k v sigma else sigma))
          (hm_empty _A2 ());;

end;; (*struct HashMap*)

module Move_Code : sig
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

let rec efficient_ancestor (_A1, _A2)
  t p c =
    (match HashMap.hm_lookup (_A1, _A2) c t with None -> false
      | Some a ->
        (let (_, aa) = a in
          HOL.eq _A1 aa p || efficient_ancestor (_A1, _A2) t p aa));;

let rec efficient_do_op (_B1, _B2)
  (Move.Move (t, newp, m, c), tree) =
    (Move.LogMove
       (t, Option.map_option (fun x -> (Product_Type.snd x, Product_Type.fst x))
             (HashMap.hm_lookup (_B1, _B2) c tree),
         newp, m, c),
      (if efficient_ancestor (_B1, _B2) tree c newp || HOL.eq _B1 c newp
        then tree
        else HashMap.hm_update (_B1, _B2) c (m, newp)
               (HashMap.g_restrict_hm_basic_ops (_B1, _B2)
                 (fun (ca, (_, _)) -> not (HOL.eq _B1 c ca)) tree)));;

let rec efficient_redo_op (_B1, _B2)
  (Move.LogMove (t, uu, p, m, c)) (ops, tree) =
    (let a = efficient_do_op (_B1, _B2) (Move.Move (t, p, m, c), tree) in
     let (op2, aa) = a in
      (op2 :: ops, aa));;

let rec efficient_undo_op (_B1, _B2)
  = function
    (Move.LogMove (t, None, newp, m, c), tree) ->
      HashMap.g_restrict_hm_basic_ops (_B1, _B2)
        (fun (ca, (_, _)) -> not (HOL.eq _B1 ca c)) tree
    | (Move.LogMove (t, Some (oldp, oldm), newp, m, c), tree) ->
        HashMap.hm_update (_B1, _B2) c (oldm, oldp)
          (HashMap.g_restrict_hm_basic_ops (_B1, _B2)
            (fun (ca, (_, _)) -> not (HOL.eq _B1 ca c)) tree);;

let rec efficient_apply_op _A (_B1, _B2)
  op1 x1 = match op1, x1 with
    op1, ([], tree1) ->
      (let a = efficient_do_op (_B1, _B2) (op1, tree1) in
       let (op2, aa) = a in
        ([op2], aa))
    | op1, (logop :: ops, tree1) ->
        (if Orderings.less
              _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
              (Move.move_time op1) (Move.log_time logop)
          then efficient_redo_op (_B1, _B2) logop
                 (efficient_apply_op _A (_B1, _B2) op1
                   (ops, efficient_undo_op (_B1, _B2) (logop, tree1)))
          else (let a = efficient_do_op (_B1, _B2) (op1, tree1) in
                let (op2, aa) = a in
                 (op2 :: logop :: ops, aa)));;

let rec efficient_apply_ops _A (_B1, _B2)
  ops = Lista.foldl
          (fun state oper -> efficient_apply_op _A (_B1, _B2) oper state)
          ([], HashMap.hm_empty _B2 ()) ops;;

end;; (*struct Move_Code*)
