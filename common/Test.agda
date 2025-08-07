module Test where

open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Default.Connectives
open import StringifyCommon.Main
open import Stringify.Main
open import Rat.Main
open import Prob.Main

getRangeProof : {{RatInRange (pos 1 ÷ 2)}} -> RatInRange (pos 1 ÷ 2)
getRangeProof {{r}} = r

exampleRangeProof : RatInRange (pos 1 ÷ 2)
exampleRangeProof = getRangeProof

exampleProb : Prob
exampleProb = record { rat = pos 1 ÷ 2; 0<=numerator<=denominator = exampleRangeProof }

postulate
    JakeIsAwesome : Set
    prob-of-jake-is-awesome : Prob-of JakeIsAwesome (mkProb ((pos 1) ÷ 2))

postulate instance
    jake-is-awesome-interp : Interpretation JakeIsAwesome "jake is awesome"

exampleStr : String
exampleStr = stringify (prob-of-jake-is-awesome)
