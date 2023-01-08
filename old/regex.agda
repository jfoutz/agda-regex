{-
Regexes don't need much in the way of structure to match.
It sure seems like a monoid is enough to match some property.
The plan here is to implement the Brzozowski derivative, and then try applying that to a bunch of monoid instances. https://en.wikipedia.org/wiki/Brzozowski_derivative

This was super helpful (to me) in unpacking the meaning of the Brzozowski derivative
https://harrisongoldste.in/languages/2017/09/30/derivatives-of-regular-expressions.html


Possibly take a run at Thompson construction, outlined by Russ Cox and see if they still work out.
https://swtch.com/~rsc/regexp/regexp1.html
-}

module regex where
{-
"∅" denotes the empty set: L(∅) = {},
"ε" denotes the singleton set containing the empty string: L(ε) = {ε},
"a" denotes the singleton set containing the single-symbol string a: L(a) = {a},
"R∨S" denotes the union of R and S: L(R∨S) = L(R) ∪ L(S),
"R∧S" denotes the intersection of R and S: L(R∧S) = L(R) ∩ L(S),
"¬R" denotes the complement of R (with respect to A*, the set of all strings over A): L(¬R) = A* \ L(R),
"RS" denotes the concatenation of R and S: L(RS) = L(R) · L(S),
"R*" denotes the Kleene closure of R: L(R*) = L(R)*.
-}
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List

open import Data.List.Base using (_++_)

open import Data.Char 

record Monoid {a} (A : Set a) : Set a where
  field
    mempty : A
    _<>_   : A -> A -> A

instance
  ListMonoid : ∀ {a} {A : Set a} -> Monoid (List A)
  ListMonoid = record { mempty = []; _<>_ = _++_ }

record Eq {a} (A : Set a) : Set a where
  field
    _=x=_ : A -> A -> Bool

instance
  CharEq : Eq Char
  CharEq = record { _=x=_ = _==_ }


data Regex (A : Set) : Set where
  ∅   : Regex A                       -- empty set
  ε   : Regex A                       -- empty container / mempty
  p_  : A -> Regex A                  -- a pattern
  _·_ : Regex A -> Regex A -> Regex A -- concatination
  _*  : Regex A -> Regex A            -- kleene star
  _∨_ : Regex A -> Regex A -> Regex A -- union
  _∧_ : Regex A -> Regex A -> Regex A -- intersection
  ¬_  : Regex A -> Regex A            -- negation - safe?


v : Regex Char -> Regex Char
v ∅ = ∅
v ε = ε
v (p x) = ∅
v (r · s) = (v r) ∧ (v s)
v (r *) = ε
v (r ∨ s) = (v r) ∨ (v s)
v (r ∧ s) = (v r) ∧ (v s)
v (¬ r) = ¬ (v r)

deriv :  Regex Char -> Char -> Regex Char
deriv ∅ c = ∅
deriv ε c = ∅
deriv (p x) c with (x == c)
...              |  true = ε
...              |  false = ∅
deriv (r · s) c = ((deriv r c) · s) ∨ ((v r) · deriv s c)
deriv (r *) c   = (deriv r c) · (r *)
deriv (r ∨ s) c = deriv r c ∨ deriv s c
deriv (r ∧ s) c = deriv r c ∧ deriv s c
deriv (¬ r) c   = ¬ (deriv r c)

abc : List Char
abc = 'a' ∷ 'b' ∷ 'c' ∷ [] 

re-1 : Regex Char
re-1 = p 'a'

re-2 : Regex Char
re-2 = re-1 ∧ re-1

re-3 : Regex Char
re-3 = p 'b'

t1 : Regex Char
t1 = deriv (deriv re-2 'b') 'a'

t2 : Regex Char
t2 = deriv (deriv re-2 'a') 'a'

t3 : Regex Char
t3 = deriv re-1 'a'

foldstr : Regex Char -> List Char -> Regex Char
foldstr r [] = r
foldstr r (c ∷ s) = foldstr (deriv r c) s

t4 : Regex Char
t4 = foldstr ((p 'a') *) ('a' ∷ 'a' ∷ 'a' ∷ [])

{-
so these aren't reduced.
i need to simplify, maybe on the way back out
maybe i should be thinking more in terms of a fold

as the string matches, the regex is the accumulator, getting picked apart rather than rolling back up.

on to https://www.ccs.neu.edu/home/turon/re-deriv.pdf
-}


