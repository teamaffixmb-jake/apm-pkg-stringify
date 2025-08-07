module Test where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Default.Connectives
open import Stringify.Main
open import Rat.Main
open import Prob.Main

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

probOfToString : (XS : String) -> (pStr : String) -> String
probOfToString XS pStr = "the probability of " ++ XS ++ " is " ++ pStr

postulate instance
    nat-interp : {n : Nat} -> Interpretation n (natToString n)
    int-interp : {i : Int} -> Interpretation i (intToString i)
    bool-interp : {b : Bool} -> Interpretation b (boolToString b)
    rat-interp : {r : Rat} -> Interpretation r (ratToString r)
    prob-interp : {p : Prob} -> Interpretation p (probToString p)
    prob-of-interp : {X : Set} -> {p : Prob} -> {XStr : String} -> {pStr : String} ->
        {{Interpretation X XStr}} -> {{Interpretation p pStr}} ->
        Interpretation (Prob-of X p) (probOfToString XStr pStr)
    prob-of-proof-interp : {X : Set} -> {p : Prob} -> {XStr : String} -> {pStr : String} -> {proof : Prob-of X p} ->
        {{Interpretation X XStr}} -> {{Interpretation p pStr}} ->
        Interpretation proof ("proof that " ++ (probOfToString XStr pStr))





postulate
    JakeIsAwesome : Set
    prob-of-jake-is-awesome : Prob-of JakeIsAwesome (mkProb ((pos 1) ÷ 2))

postulate instance
    jake-is-awesome-interp : Interpretation JakeIsAwesome "jake is awesome"



exampleStr : String
exampleStr = stringify (prob-of-jake-is-awesome)
