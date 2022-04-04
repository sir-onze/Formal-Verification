module Length where

import qualified Prelude

data Nat =
   O
 | S Nat

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

correct_ln :: ([] Z) -> Nat
correct_ln l =
  case l of {
   [] -> O;
   (:) _ l0 -> S (correct_ln l0)}

