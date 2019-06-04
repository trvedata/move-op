structure Ancestor : sig
  type 'a equal
  type 'a set
  val ancestor :
    'a equal -> 'b equal -> ('a * ('b * 'a)) set -> 'a -> 'a -> bool
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

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun meta B_ t = sup_seta B_ (image (fn (_, (m, _)) => insert B_ m bot_set) t);

fun support A_ t =
  sup_seta A_ (image (fn (p, (_, c)) => insert A_ p (insert A_ c bot_set)) t);

fun ancestor A_ B_ tree parent child =
  bex (meta B_ tree)
    (fn m =>
      member (equal_prod A_ (equal_prod B_ A_)) (parent, (m, child))
        tree) orelse
    bex (meta B_ tree)
      (fn m =>
        bex (support A_ tree)
          (fn anc =>
            member (equal_prod A_ (equal_prod B_ A_)) (parent, (m, anc))
              tree andalso
              ancestor A_ B_ tree anc child));

end; (*struct Ancestor*)
