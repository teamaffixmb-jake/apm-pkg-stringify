module Stringify.Main where

open import Agda.Builtin.String
open import Agda.Primitive

-- Create the type of proofs that a value's interpretation is a given string,
-- and do not provide any ways of constructing it.
-- Inhabitants of this type must be postulated as they are fundamentally interpretational.
postulate
    Interpretation : {α : Level} -> {A : Set α} -> (a : A) -> String -> Set

stringify : {aStr : String} {α : Level} {A : Set α} -> (a : A) -> ⦃ Interpretation a aStr ⦄ -> String
stringify {aStr} x = aStr
