module re where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Data.Bool
open import Data.Char

data Re (A : Set) : Set where
  empty : Re A
  terminal : A -> Re A
  concat : Re A -> Re A -> Re A
  alternate : Re A -> Re A -> Re A
  kleene : Re A -> Re A

abr : Re Char
abr = concat (terminal 'a') (terminal 'b')

as : List Char
as = 'a' ∷ []

abs : List Char
abs = 'a' ∷ 'b' ∷ []

abcs : List Char
abcs = 'a' ∷ 'b' ∷ 'c' ∷ []

estr : Re Char
estr = kleene empty

obs : Re Char -> Bool
obs empty = false
obs (terminal x) = false
obs (concat r1 r2) = obs r1 ∧ obs r2
obs (alternate r1 r2) = obs r1 ∨ obs r2
obs (kleene r) = true

deriv : Re Char -> Char -> Re Char
deriv empty c = empty
deriv (terminal x) c  with (x == c)
...                       | true = estr
...                       | false = empty
deriv (alternate r1 r2) c = alternate (deriv r1 c) (deriv r2 c)
deriv (concat r1 r2) c = alternate (concat (deriv r1 c) r2) (concat help  (deriv r2 c))
  where help = if obs r1 then estr else empty
deriv (kleene r) c = concat (deriv r c) (kleene r)

derivStr : Re Char -> List Char -> Re Char
derivStr r [] = r
derivStr r (x ∷ s) = derivStr (deriv r x) s

match : Re Char -> List Char -> Bool
match r s = obs (derivStr r s)

  
