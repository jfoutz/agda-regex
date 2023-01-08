module regex where
{-
  see,
  https://www.ccs.neu.edu/home/turon/re-deriv.pdf
-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Data.Char using (_==_)

data Regex : Set where
  ∅      : Regex
  ε      : Regex
  _∈     : Char  -> Regex -- because i can, and it's kind of hilarious.
  _·_    : Regex -> Regex -> Regex
  _*     : Regex -> Regex
  _+_    : Regex -> Regex -> Regex
  _&_    : Regex -> Regex -> Regex
  ¬_     : Regex -> Regex

infix 20 _·_
infix 15 _&_
infix 10 _+_

{- maybe dfa
 Q - states
 Q0 - start
 F - final states
 d - changes/transiton functions
 -}


v : Regex -> Regex
v ∅ = ∅
v ε = ε
v (x ∈) = ∅
v (r · s) = v r & v s
v (r *) = ε
v (r + s) = v r + v s
v (r & s) = v r & v s
v (¬ ∅) = ε
v (¬ ε) = ∅
v (¬ r) = {!!}



deriv : Char -> Regex -> Regex
deriv c ∅ = ∅
deriv c ε = ∅
deriv c (x ∈) with c == x
...              | true = ε
...              | false = ∅
deriv c (r · s) = ((deriv c r) · s) + ((v r) · (deriv c s))
deriv c (r *) = (deriv c r) · (r *)
deriv c (r + s) = (deriv c r) + (deriv c s)
deriv c (r & s) = (deriv c r) & (deriv c s)
deriv c (¬ r) = ¬ (deriv c r)




