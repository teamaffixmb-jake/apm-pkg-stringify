module StringifyCommon.Main where

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

postulate instance
    nat-interp : {n : Nat} -> Interpretation n (primShowNat n)
    int-interp : {i : Int} -> Interpretation i (primShowInteger i)
    false-interp : Interpretation false "false"
    true-interp : Interpretation true "true"
    rat-interp : {r : Rat} -> Interpretation r (primShowInteger (Rat.num r) ++ "/" ++ primShowNat (Rat.den r))
    prob-interp : {r : Rat} {rStr : String} -> {{rir : RatInRange r}} -> {{Interpretation r rStr}} -> Interpretation (mkProb r) rStr
    prob-of-interp : {X : Set} {p : Prob} {XStr : String} {pStr : String} ->
        {{Interpretation X XStr}} -> {{Interpretation p pStr}} ->
        Interpretation (Prob-of X p) ("the probability of " ++ XStr ++ " is " ++ pStr)
    prob-of-proof-interp : {X : Set} {p : Prob} {proof : Prob-of X p} {typeStr : String} ->
        {{Interpretation (Prob-of X p) typeStr}} ->
        Interpretation proof ("proof that " ++ typeStr)
