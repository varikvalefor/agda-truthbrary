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

module apDec where
  apDec' : ∀ {a b p}
         → {A : Set a} → {B : Set b}
         → {P : A → Set p}
         → (f : (x : A) → P x → B)
         → (x : A)
         → Dec $ P x
         → Maybe B
  apDec' f x (yes p) = just $ f x p
  apDec' _ _ _ = nothing

  apDec : ∀ {a b p}
        → {A : Set a} → {B : Set b}
        → {P : A → Set p}
        → (f : (x : A) → P x → B)
        → (P? : Decidable P)
        → A
        → Maybe B
  apDec f P? x = apDec' f x $ P? x

apDec = apDec.apDec

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

  readMaybe = apDec (Read.read rr) P?

  field
    justys : (x : Strong)
           → Read.P rr x
           → Is-just $ readMaybe x
\end{code}
