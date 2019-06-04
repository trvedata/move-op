module Ancestor(Set, ancestor) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Set a = Set [a] | Coset [a];

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

bot_set :: forall a. Set a;
bot_set = Set [];

sup_seta :: forall a. (Eq a) => Set (Set a) -> Set a;
sup_seta (Set xs) = fold sup_set xs bot_set;

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

meta :: forall a b. (Eq b) => Set (a, (b, a)) -> Set b;
meta t = sup_seta (image (\ (_, (m, _)) -> insert m bot_set) t);

children :: forall a b. (Eq a) => Set (a, (b, a)) -> Set a;
children t = sup_seta (image (\ (_, (_, c)) -> insert c bot_set) t);

ancestor :: forall a b. (Eq a, Eq b) => a -> a -> Set (a, (b, a)) -> Bool;
ancestor parent child tree =
  bex (meta tree) (\ m -> member (parent, (m, child)) tree) ||
    bex (meta tree)
      (\ m ->
        bex (children tree)
          (\ anc -> member (parent, (m, anc)) tree && ancestor anc child tree));

}
