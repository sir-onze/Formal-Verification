module Exemplo4 where

import qualified Prelude

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig2 a = a
  -- singleton inductive, whose constructor was exist2
  
data Sumbool =
   Left
 | Right

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec =
  z_lt_dec

insert :: Z -> ([] Z) -> [] Z
insert x l =
  case l of {
   [] -> (:) x [];
   (:) h t ->
    case z_lt_ge_dec x h of {
     Left -> (:) x ((:) h t);
     Right -> (:) h (insert x t)}}

inssort :: ([] Z) -> Sig2 ([] Z)
inssort l =
  case l of {
   [] -> [];
   (:) y l0 -> insert y (inssort l0)}

