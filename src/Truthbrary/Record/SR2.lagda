\begin{code}
module Truthbrary.Record.SR2 where

open import Level
  using (
    _⊔_;
    suc
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    _⊎_
  )
open import Function
  using (
    _∘_;
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
    Is-nothing;
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Data.Product
  using (
    _×_
  )
open import Relation.Unary
  using (
    Decidable;
    _⊆_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Data.List.Relation.Unary.All
  as 𝕃All
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
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

  open Read rr

  readMaybe = apDec read P?

  field
    justys : P ⊆ (Is-just ∘ readMaybe)
    nad : (¬_ ∘ P) ⊆ (Is-nothing ∘ readMaybe)

instance
  readNat : Read {p = Level.zero} ℕ
  readNat = record {
    P = λ n →
      (_⊎_ (djm0 n) (ml0 n));
    read = {!!}
    }
    where
    IsDigit : Char → Set
    djm0 : Strong → Set
    djm0 n = 𝕃All.All IsDigit n
    ml0 : Strong → Set
    ml0 n = 
      (_×_
        (𝕃.head n ≡ just '-')
        (_×_
          (¬_ $ 𝕃.head (𝕃.drop 1 n) ≡ nothing)
          (𝕃All.All IsDigit $ 𝕃.drop 1 n)))
    IsDigit = λ x →
      (𝕃.foldr
        _⊎_
        (x ≡ x)
        (𝕃.map
          (x ≡_)
          ('0' ∷
           '1' ∷
           '2' ∷
           '3' ∷
           '4' ∷
           '5' ∷
           '6' ∷
           '7' ∷
           '8' ∷
           '9' ∷
           [])))
\end{code}
