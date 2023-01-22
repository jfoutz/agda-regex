module regex where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

record Eq {a} (A : Set a) : Set a where
  field
    _eq_ : A -> A -> Bool

open Eq {{...}} public

  
same : Bool -> Bool -> Bool
same false false = true
same false true = false
same true false = false
same true true = true

instance
  BoolEq : Eq Bool
  _eq_ {{BoolEq}} = same 

instance
  NatEq : Eq Nat
  NatEq = record { _eq_ = _==_ }

member : ∀ {a} {A : Set a} -> {{ Eq A }} ->  List A -> A -> Bool
member [] n = false
member (x ∷ l) n with ( n eq x )
...                 | true = true
...                 | false = member l n

add-item : List Nat -> Nat -> List Nat
add-item l n with (member l n)
...             | true = l
...             | false = n ∷ l

-- ok. we've got something set like so we can specify an alphabet.











