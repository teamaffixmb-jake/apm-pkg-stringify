module Test where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Stringify.Main
open import Rat.Main
open import Prob.Main

open Stringified

private
    _++_ : String -> String -> String
    _++_ = primStringAppend
    infixr 5 _++_

natToString : Nat -> String
natToString n = primShowNat n

intToString : Int -> String
intToString i = primShowInteger i

boolToString : Bool -> String
boolToString true = "true"
boolToString false = "false"

ratToString : Rat -> String
ratToString r = primShowInteger (Rat.num r) ++ "/" ++ primShowNat (Rat.den r)

probToString : Prob -> String
probToString p = ratToString (Prob.rat p)

probOfToString : {X : Set} {p : Prob} -> {{Stringified X}} -> Prob-of X p -> String
probOfToString {X} {p} {{sX}} proof = "the probability of " ++ val sX ++ " is " ++ probToString p

postulate
    nat-stringifies : {n : Nat} -> Interpretation n (natToString n)
    int-stringifies : {i : Int} -> Interpretation i (intToString i)
    bool-stringifies : {b : Bool} -> Interpretation b (boolToString b)
    rat-stringifies : {r : Rat} -> Interpretation r (ratToString r)
    prob-stringifies : {p : Prob} -> Interpretation p (probToString p)
    prob-of-stringifies : {X : Set} -> {p : Prob} -> {XStr : String} -> {pStr : String} ->
        Interpretation X XStr -> Interpretation p pStr ->
        Interpretation (Prob-of X p) ("the probability of " ++ XStr ++ " is " ++ pStr)
    proof-stringifies : {X : Set} -> {p : Prob} -> {XStr : String} -> {pStr : String} -> {proof : Prob-of X p} ->
        Interpretation X XStr -> Interpretation p pStr ->
        Interpretation proof ("proof that the probability of " ++ XStr ++ " is " ++ pStr)
    
instance
  showNat : {n : Nat} -> Stringified n
  showNat {n} = mkStringified (nat-stringifies {n})

  showInt : {i : Int} -> Stringified i
  showInt {i} = mkStringified (int-stringifies {i})

  showBool : {b : Bool} -> Stringified b
  showBool {b} = mkStringified (bool-stringifies {b})

  showRat : {r : Rat} -> Stringified r
  showRat {r} = mkStringified (rat-stringifies {r})

  showProb : {p : Prob} -> Stringified p
  showProb {p} = mkStringified (prob-stringifies {p})

  showProb-of : {X : Set} {p : Prob} -> {{Stringified X}} -> {{Stringified p}} -> Stringified (Prob-of X p)
  showProb-of {{sX}} {{sp}} = mkStringified (prob-of-stringifies (interp sX) (interp sp))

  show-proof-that-prob-of : {X : Set} {p : Prob} {x : Prob-of X p} -> 
    {{Stringified X}} -> {{Stringified p}} ->
    Stringified x
  show-proof-that-prob-of {{sX}} {{sp}} = mkStringified (proof-stringifies (interp sX) (interp sp))

stringify : {α : Level} -> {A : Set α} -> (a : A) -> ⦃ Stringified a ⦄ -> String
stringify x {{s}} = val s

exampleStr : String
exampleStr = stringify (negsuc 0)
