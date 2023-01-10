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
deriv c (r · s) = deriv c r · s + v r · deriv c s
deriv c (r *)   = deriv c r · (r *)
deriv c (r + s) = deriv c r + deriv c s
deriv c (r & s) = deriv c r & deriv c s
deriv c (¬ r) = ¬ deriv c r



t1 : Regex
t1 = deriv 'a' ('a' ∈)
t2 : Regex
t2 = deriv 'b' ('a' ∈)
t3 : Regex
t3 = deriv 'a' ('a' ∈) + ('b' ∈)
t4 : Regex
t4 = deriv 'a' ('a' ∈) & ('b' ∈)

{- so this works, i feel sorta like there should be a simplify step at this point. ε & ∅ should probably just be ∅
   putting a pin in that for now
-}
tex1 : Regex
tex1 = deriv 'a' (('a' ∈) · (('b' ∈)*))
tex2 : Regex
tex2 = deriv 'b' tex1
tex3 : Regex
tex3 = deriv 'b' tex1

tex5 : Regex
tex5 = deriv 'a' (('a' ∈) · ('b' ∈) & ('a' ∈) · ('c' ∈))
--  -> (ε · ('b' ∈) + ∅ · ∅) & (ε · ('c' ∈) + ∅ · ∅)

cancel : Regex -> Regex
cancel ∅ = ∅
cancel ε = ε
cancel (x ∈) = x ∈
cancel (∅ · _) = ∅
cancel (_ · ∅) = ∅
cancel (r · s) = (cancel r) · (cancel s)
cancel (r *) = r *
cancel (∅ + s) = (cancel s)
cancel (r + ∅) = (cancel r)
cancel (r + s) = (cancel r) + (cancel s)
cancel (_ & ∅) = ∅
cancel (∅ & _) = ∅
cancel (r & s) = (cancel r) & (cancel s)
cancel (¬ r) = ¬ r

tex5c : Regex
tex5c = cancel tex5
-- -> (ε · ('b' ∈) + ∅) & (ε · ('c' ∈) + ∅)
{- it has already matched!
   that's why
   eh, maybe accumulator style or something. er, corecursion
   it's fine. there's nothing _wrong_
   it's just doing extra uneeded junk -}

open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.String
open import Data.Vec
open import Agda.Builtin.Nat

dstr : {n : Nat} -> Regex -> Vec Char n -> Regex
dstr r [] = r
dstr r (c ∷ s) = dstr (deriv c r) s

wrap : Regex -> String  -> Regex
wrap r s = dstr r (toVec s)


ts1 : Regex
ts1 = cancel (wrap (('a' ∈)*) "aaa")

{- ok. vector of vectors.
 [ s1 : [ 'a' -> s2, 'b' -> s3]
   s2 : [ 'b' -> s3]]
 something like that.
 index by state number, children indexed by transition item.

 this isn't a fantastic solution, but i think it's a solution
 i can make progress with.
 bleh.
-}

{-
record Dfa:Set where
  states :
  alphabet :
  transition :
  start :
  accept :
-}

open import Agda.Builtin.Sigma

stuff : Regex -> List Char -> {!!} -> {!!}
stuff r a = map (\ c -> deriv c r)





