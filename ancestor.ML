structure Ancestor : sig
  type 'a equal
  type int
  type 'a person_ext
  type 'a set
  val ancestor : 'a equal -> ('a * 'a) set -> 'a -> 'a -> bool
  val mk_person : string -> int -> unit person_ext
  val has_ancestor : 'a equal -> ('a * 'a) set -> 'a -> bool
  val has_descendent : 'a equal -> ('a * 'a) set -> 'a -> bool
  val have_common_ancestor :
    (unit person_ext * unit person_ext) set ->
      unit person_ext -> unit person_ext -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

datatype int = Int_of_integer of IntInf.int;

datatype 'a person_ext = Person_ext of string * int * 'a;

fun integer_of_int (Int_of_integer k) = k;

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

fun equal_person_exta A_ (Person_ext (namea, agea, morea))
  (Person_ext (name, age, more)) =
  ((namea : string) = name) andalso
    (equal_int agea age andalso eq A_ morea more);

fun equal_person_ext A_ = {equal = equal_person_exta A_} : 'a person_ext equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

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

val bot_set : 'a set = Set [];

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun support A_ ss =
  sup_seta A_ (image (fn (x, y) => insert A_ x (insert A_ y bot_set)) ss);

fun ancestor A_ ss p c =
  member (equal_prod A_ A_) (p, c) ss orelse
    bex ss (fn (x, y) => eq A_ p x andalso ancestor A_ ss y c);

fun mk_person n a = Person_ext (n, a, ());

fun has_ancestor A_ ss c = bex (support A_ ss) (fn a => ancestor A_ ss a c);

fun has_descendent A_ ss p = bex (support A_ ss) (ancestor A_ ss p);

fun have_common_ancestor ss c1 c2 =
  bex (support (equal_person_ext equal_unit) ss)
    (fn a =>
      ancestor (equal_person_ext equal_unit) ss a c1 andalso
        ancestor (equal_person_ext equal_unit) ss a c2);

end; (*struct Ancestor*)
