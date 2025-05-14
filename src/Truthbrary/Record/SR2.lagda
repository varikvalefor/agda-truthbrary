\begin{code}
module Truthbrary.Record.SR2 where

open import Level
  using (
    _⊔_;
    suc
  )
open import Function
  using (
    _$_
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Relation.Unary
  using (
    Decidable
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )

record Read {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    P : Strong → Set p
    read : (x : Strong) → P x → A

record ReadMaybe {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    rr : Read {p = p} A
    P? : Decidable $ Read.P rr

  readMaybePrivate : (x : Strong)
                   → Dec $ Read.P rr x
                   → Maybe A
  readMaybePrivate x (yes p) = just $ Read.read rr x p
  readMaybePrivate _ _ = nothing

  readMaybe : Strong → Maybe A
  readMaybe x = readMaybePrivate x $ P? x

record ReadMaybe! {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    rm : ReadMaybe {p = p} A

  open ReadMaybe rm
  open Read (ReadMaybe.rr rm)

  field
    justys : (x : Strong)
           → P x
           → Is-just $ readMaybe x
\end{code}
