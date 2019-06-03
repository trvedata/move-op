structure Ancestor : sig
  type 'a equal
  type 'a set
  val ancestor : 'a equal -> ('a * 'a) set -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun ancestor A_ ss p c =
  member (equal_prod A_ A_) (p, c) ss orelse
    bex ss (fn (x, y) => eq A_ p x andalso ancestor A_ ss y c);

end; (*struct Ancestor*)
