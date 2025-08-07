module Stringify.Main where

open import Agda.Builtin.String
open import Agda.Primitive

-- Create the type of proofs that a value's interpretation is a given string,
-- and do not provide any ways of constructing it.
-- Inhabitants of this type must be postulated as they are fundamentally interpretational.
postulate
    Interpretation : {α : Level} -> {A : Set α} -> (a : A) -> String -> Set

-- Instance-searchable record that contains a postulated proof that a value's interpretation is a given string.
record Stringified {α : Level} {A : Set α} (a : A) : Set α where
    field
        val : String
        interp : Interpretation a val

open Stringified

mkStringified : {val : String} {α : Level} {A : Set α} {a : A} -> (interp : Interpretation a val) -> Stringified a
mkStringified {val} {α} {A} {a} interp .val = val
mkStringified {val} {α} {A} {a} interp .interp = interp
