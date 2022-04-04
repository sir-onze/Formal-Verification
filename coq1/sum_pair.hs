module Sum_pair where

import qualified Prelude

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

correct_sum_pair :: ([] (Prod Nat Nat)) -> Nat
correct_sum_pair l =
  case l of {
   [] -> O;
   (:) y l0 -> case y of {
                Pair _ x -> add x (correct_sum_pair l0)}}

