structure Ancestor : sig
  type char
  type 'a set
  val ancestora : bool
end = struct

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

val enum_chara : char list =
  [Chara (false, false, false, false, false, false, false, false),
    Chara (true, false, false, false, false, false, false, false),
    Chara (false, true, false, false, false, false, false, false),
    Chara (true, true, false, false, false, false, false, false),
    Chara (false, false, true, false, false, false, false, false),
    Chara (true, false, true, false, false, false, false, false),
    Chara (false, true, true, false, false, false, false, false),
    Chara (true, true, true, false, false, false, false, false),
    Chara (false, false, false, true, false, false, false, false),
    Chara (true, false, false, true, false, false, false, false),
    Chara (false, true, false, true, false, false, false, false),
    Chara (true, true, false, true, false, false, false, false),
    Chara (false, false, true, true, false, false, false, false),
    Chara (true, false, true, true, false, false, false, false),
    Chara (false, true, true, true, false, false, false, false),
    Chara (true, true, true, true, false, false, false, false),
    Chara (false, false, false, false, true, false, false, false),
    Chara (true, false, false, false, true, false, false, false),
    Chara (false, true, false, false, true, false, false, false),
    Chara (true, true, false, false, true, false, false, false),
    Chara (false, false, true, false, true, false, false, false),
    Chara (true, false, true, false, true, false, false, false),
    Chara (false, true, true, false, true, false, false, false),
    Chara (true, true, true, false, true, false, false, false),
    Chara (false, false, false, true, true, false, false, false),
    Chara (true, false, false, true, true, false, false, false),
    Chara (false, true, false, true, true, false, false, false),
    Chara (true, true, false, true, true, false, false, false),
    Chara (false, false, true, true, true, false, false, false),
    Chara (true, false, true, true, true, false, false, false),
    Chara (false, true, true, true, true, false, false, false),
    Chara (true, true, true, true, true, false, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, false, false),
    Chara (false, false, true, false, false, true, false, false),
    Chara (true, false, true, false, false, true, false, false),
    Chara (false, true, true, false, false, true, false, false),
    Chara (true, true, true, false, false, true, false, false),
    Chara (false, false, false, true, false, true, false, false),
    Chara (true, false, false, true, false, true, false, false),
    Chara (false, true, false, true, false, true, false, false),
    Chara (true, true, false, true, false, true, false, false),
    Chara (false, false, true, true, false, true, false, false),
    Chara (true, false, true, true, false, true, false, false),
    Chara (false, true, true, true, false, true, false, false),
    Chara (true, true, true, true, false, true, false, false),
    Chara (false, false, false, false, true, true, false, false),
    Chara (true, false, false, false, true, true, false, false),
    Chara (false, true, false, false, true, true, false, false),
    Chara (true, true, false, false, true, true, false, false),
    Chara (false, false, true, false, true, true, false, false),
    Chara (true, false, true, false, true, true, false, false),
    Chara (false, true, true, false, true, true, false, false),
    Chara (true, true, true, false, true, true, false, false),
    Chara (false, false, false, true, true, true, false, false),
    Chara (true, false, false, true, true, true, false, false),
    Chara (false, true, false, true, true, true, false, false),
    Chara (true, true, false, true, true, true, false, false),
    Chara (false, false, true, true, true, true, false, false),
    Chara (true, false, true, true, true, true, false, false),
    Chara (false, true, true, true, true, true, false, false),
    Chara (true, true, true, true, true, true, false, false),
    Chara (false, false, false, false, false, false, true, false),
    Chara (true, false, false, false, false, false, true, false),
    Chara (false, true, false, false, false, false, true, false),
    Chara (true, true, false, false, false, false, true, false),
    Chara (false, false, true, false, false, false, true, false),
    Chara (true, false, true, false, false, false, true, false),
    Chara (false, true, true, false, false, false, true, false),
    Chara (true, true, true, false, false, false, true, false),
    Chara (false, false, false, true, false, false, true, false),
    Chara (true, false, false, true, false, false, true, false),
    Chara (false, true, false, true, false, false, true, false),
    Chara (true, true, false, true, false, false, true, false),
    Chara (false, false, true, true, false, false, true, false),
    Chara (true, false, true, true, false, false, true, false),
    Chara (false, true, true, true, false, false, true, false),
    Chara (true, true, true, true, false, false, true, false),
    Chara (false, false, false, false, true, false, true, false),
    Chara (true, false, false, false, true, false, true, false),
    Chara (false, true, false, false, true, false, true, false),
    Chara (true, true, false, false, true, false, true, false),
    Chara (false, false, true, false, true, false, true, false),
    Chara (true, false, true, false, true, false, true, false),
    Chara (false, true, true, false, true, false, true, false),
    Chara (true, true, true, false, true, false, true, false),
    Chara (false, false, false, true, true, false, true, false),
    Chara (true, false, false, true, true, false, true, false),
    Chara (false, true, false, true, true, false, true, false),
    Chara (true, true, false, true, true, false, true, false),
    Chara (false, false, true, true, true, false, true, false),
    Chara (true, false, true, true, true, false, true, false),
    Chara (false, true, true, true, true, false, true, false),
    Chara (true, true, true, true, true, false, true, false),
    Chara (false, false, false, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, false, true, false, true, true, false),
    Chara (true, true, false, true, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, true, true, true, false),
    Chara (true, false, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, true, true, false, true, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, true, true, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, true, false, true, true, true, true, false),
    Chara (true, true, false, true, true, true, true, false),
    Chara (false, false, true, true, true, true, true, false),
    Chara (true, false, true, true, true, true, true, false),
    Chara (false, true, true, true, true, true, true, false),
    Chara (true, true, true, true, true, true, true, false),
    Chara (false, false, false, false, false, false, false, true),
    Chara (true, false, false, false, false, false, false, true),
    Chara (false, true, false, false, false, false, false, true),
    Chara (true, true, false, false, false, false, false, true),
    Chara (false, false, true, false, false, false, false, true),
    Chara (true, false, true, false, false, false, false, true),
    Chara (false, true, true, false, false, false, false, true),
    Chara (true, true, true, false, false, false, false, true),
    Chara (false, false, false, true, false, false, false, true),
    Chara (true, false, false, true, false, false, false, true),
    Chara (false, true, false, true, false, false, false, true),
    Chara (true, true, false, true, false, false, false, true),
    Chara (false, false, true, true, false, false, false, true),
    Chara (true, false, true, true, false, false, false, true),
    Chara (false, true, true, true, false, false, false, true),
    Chara (true, true, true, true, false, false, false, true),
    Chara (false, false, false, false, true, false, false, true),
    Chara (true, false, false, false, true, false, false, true),
    Chara (false, true, false, false, true, false, false, true),
    Chara (true, true, false, false, true, false, false, true),
    Chara (false, false, true, false, true, false, false, true),
    Chara (true, false, true, false, true, false, false, true),
    Chara (false, true, true, false, true, false, false, true),
    Chara (true, true, true, false, true, false, false, true),
    Chara (false, false, false, true, true, false, false, true),
    Chara (true, false, false, true, true, false, false, true),
    Chara (false, true, false, true, true, false, false, true),
    Chara (true, true, false, true, true, false, false, true),
    Chara (false, false, true, true, true, false, false, true),
    Chara (true, false, true, true, true, false, false, true),
    Chara (false, true, true, true, true, false, false, true),
    Chara (true, true, true, true, true, false, false, true),
    Chara (false, false, false, false, false, true, false, true),
    Chara (true, false, false, false, false, true, false, true),
    Chara (false, true, false, false, false, true, false, true),
    Chara (true, true, false, false, false, true, false, true),
    Chara (false, false, true, false, false, true, false, true),
    Chara (true, false, true, false, false, true, false, true),
    Chara (false, true, true, false, false, true, false, true),
    Chara (true, true, true, false, false, true, false, true),
    Chara (false, false, false, true, false, true, false, true),
    Chara (true, false, false, true, false, true, false, true),
    Chara (false, true, false, true, false, true, false, true),
    Chara (true, true, false, true, false, true, false, true),
    Chara (false, false, true, true, false, true, false, true),
    Chara (true, false, true, true, false, true, false, true),
    Chara (false, true, true, true, false, true, false, true),
    Chara (true, true, true, true, false, true, false, true),
    Chara (false, false, false, false, true, true, false, true),
    Chara (true, false, false, false, true, true, false, true),
    Chara (false, true, false, false, true, true, false, true),
    Chara (true, true, false, false, true, true, false, true),
    Chara (false, false, true, false, true, true, false, true),
    Chara (true, false, true, false, true, true, false, true),
    Chara (false, true, true, false, true, true, false, true),
    Chara (true, true, true, false, true, true, false, true),
    Chara (false, false, false, true, true, true, false, true),
    Chara (true, false, false, true, true, true, false, true),
    Chara (false, true, false, true, true, true, false, true),
    Chara (true, true, false, true, true, true, false, true),
    Chara (false, false, true, true, true, true, false, true),
    Chara (true, false, true, true, true, true, false, true),
    Chara (false, true, true, true, true, true, false, true),
    Chara (true, true, true, true, true, true, false, true),
    Chara (false, false, false, false, false, false, true, true),
    Chara (true, false, false, false, false, false, true, true),
    Chara (false, true, false, false, false, false, true, true),
    Chara (true, true, false, false, false, false, true, true),
    Chara (false, false, true, false, false, false, true, true),
    Chara (true, false, true, false, false, false, true, true),
    Chara (false, true, true, false, false, false, true, true),
    Chara (true, true, true, false, false, false, true, true),
    Chara (false, false, false, true, false, false, true, true),
    Chara (true, false, false, true, false, false, true, true),
    Chara (false, true, false, true, false, false, true, true),
    Chara (true, true, false, true, false, false, true, true),
    Chara (false, false, true, true, false, false, true, true),
    Chara (true, false, true, true, false, false, true, true),
    Chara (false, true, true, true, false, false, true, true),
    Chara (true, true, true, true, false, false, true, true),
    Chara (false, false, false, false, true, false, true, true),
    Chara (true, false, false, false, true, false, true, true),
    Chara (false, true, false, false, true, false, true, true),
    Chara (true, true, false, false, true, false, true, true),
    Chara (false, false, true, false, true, false, true, true),
    Chara (true, false, true, false, true, false, true, true),
    Chara (false, true, true, false, true, false, true, true),
    Chara (true, true, true, false, true, false, true, true),
    Chara (false, false, false, true, true, false, true, true),
    Chara (true, false, false, true, true, false, true, true),
    Chara (false, true, false, true, true, false, true, true),
    Chara (true, true, false, true, true, false, true, true),
    Chara (false, false, true, true, true, false, true, true),
    Chara (true, false, true, true, true, false, true, true),
    Chara (false, true, true, true, true, false, true, true),
    Chara (true, true, true, true, true, false, true, true),
    Chara (false, false, false, false, false, true, true, true),
    Chara (true, false, false, false, false, true, true, true),
    Chara (false, true, false, false, false, true, true, true),
    Chara (true, true, false, false, false, true, true, true),
    Chara (false, false, true, false, false, true, true, true),
    Chara (true, false, true, false, false, true, true, true),
    Chara (false, true, true, false, false, true, true, true),
    Chara (true, true, true, false, false, true, true, true),
    Chara (false, false, false, true, false, true, true, true),
    Chara (true, false, false, true, false, true, true, true),
    Chara (false, true, false, true, false, true, true, true),
    Chara (true, true, false, true, false, true, true, true),
    Chara (false, false, true, true, false, true, true, true),
    Chara (true, false, true, true, false, true, true, true),
    Chara (false, true, true, true, false, true, true, true),
    Chara (true, true, true, true, false, true, true, true),
    Chara (false, false, false, false, true, true, true, true),
    Chara (true, false, false, false, true, true, true, true),
    Chara (false, true, false, false, true, true, true, true),
    Chara (true, true, false, false, true, true, true, true),
    Chara (false, false, true, false, true, true, true, true),
    Chara (true, false, true, false, true, true, true, true),
    Chara (false, true, true, false, true, true, true, true),
    Chara (true, true, true, false, true, true, true, true),
    Chara (false, false, false, true, true, true, true, true),
    Chara (true, false, false, true, true, true, true, true),
    Chara (false, true, false, true, true, true, true, true),
    Chara (true, true, false, true, true, true, true, true),
    Chara (false, false, true, true, true, true, true, true),
    Chara (true, false, true, true, true, true, true, true),
    Chara (false, true, true, true, true, true, true, true),
    Chara (true, true, true, true, true, true, true, true)];

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun enum_all_char p = list_all p enum_chara;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun enum_ex_char p = list_ex p enum_chara;

type 'a finite = {};

type 'a enum =
  {finite_enum : 'a finite, enum : 'a list, enum_all : ('a -> bool) -> bool,
    enum_ex : ('a -> bool) -> bool};
val finite_enum = #finite_enum : 'a enum -> 'a finite;
val enum = #enum : 'a enum -> 'a list;
val enum_all = #enum_all : 'a enum -> ('a -> bool) -> bool;
val enum_ex = #enum_ex : 'a enum -> ('a -> bool) -> bool;

val finite_char = {} : char finite;

val enum_char =
  {finite_enum = finite_char, enum = enum_chara, enum_all = enum_all_char,
    enum_ex = enum_ex_char}
  : char enum;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_char = {equal = equal_chara} : char equal;

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

val ancestora : bool =
  ancestor (enum_char, equal_char)
    (insert (equal_prod equal_char equal_char)
      (Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false))
      (insert (equal_prod equal_char equal_char)
        (Chara (false, true, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false))
        (insert (equal_prod equal_char equal_char)
          (Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false))
          bot_set)))
    (Chara (true, false, false, false, false, true, true, false))
    (Chara (false, false, true, false, false, true, true, false));

end; (*struct Ancestor*)
