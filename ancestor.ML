structure Ancestor : sig
  type 'a enum
  type 'a equal
  type 'a set
  val ancestor : 'a enum * 'a equal -> ('a * 'a) set -> 'a -> 'a -> bool
end = struct

type 'a finite = {};

type 'a enum =
  {finite_enum : 'a finite, enum : 'a list, enum_all : ('a -> bool) -> bool,
    enum_ex : ('a -> bool) -> bool};
val finite_enum = #finite_enum : 'a enum -> 'a finite;
val enum = #enum : 'a enum -> 'a list;
val enum_all = #enum_all : 'a enum -> ('a -> bool) -> bool;
val enum_ex = #enum_ex : 'a enum -> ('a -> bool) -> bool;

fun enum_all_prod A_ B_ p =
  enum_all A_ (fn x => enum_all B_ (fn y => p (x, y)));

fun enum_ex_prod A_ B_ p = enum_ex A_ (fn x => enum_ex B_ (fn y => p (x, y)));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun product [] uu = []
  | product (x :: xs) ys = map (fn a => (x, a)) ys @ product xs ys;

fun enum_proda A_ B_ = product (enum A_) (enum B_);

fun finite_prod A_ B_ = {} : ('a * 'b) finite;

fun enum_prod A_ B_ =
  {finite_enum = finite_prod (finite_enum A_) (finite_enum B_),
    enum = enum_proda A_ B_, enum_all = enum_all_prod A_ B_,
    enum_ex = enum_ex_prod A_ B_}
  : ('a * 'b) enum;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun ex A_ p = enum_ex A_ p;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun collect A_ p = Set (filter p (enum A_));

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun whilea b c s = (if b s then whilea b c (c s) else s);

val bot_set : 'a set = Set [];

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun less_eq_set A_ (Coset []) (Set []) = false
  | less_eq_set A_ a (Coset ys) = list_all (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Set xs) b = list_all (fn x => member A_ x b) xs;

fun equal_set A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun ancestor (A1_, A2_) s p c =
  member (equal_prod A2_ A2_) (p, c)
    (whilea
      (fn a =>
        not (equal_set (equal_prod A2_ A2_)
              (sup_set (equal_prod A2_ A2_) s
                (collect (enum_prod A1_ A1_)
                  (fn (pa, g) =>
                    ex A1_
                      (fn ca =>
                        member (equal_prod A2_ A2_) (pa, ca) s andalso
                          member (equal_prod A2_ A2_) (ca, g) a))))
              a))
      (fn t =>
        sup_set (equal_prod A2_ A2_) s
          (collect (enum_prod A1_ A1_)
            (fn (pa, g) =>
              ex A1_
                (fn ca =>
                  member (equal_prod A2_ A2_) (pa, ca) s andalso
                    member (equal_prod A2_ A2_) (ca, g) t))))
      bot_set);

end; (*struct Ancestor*)
