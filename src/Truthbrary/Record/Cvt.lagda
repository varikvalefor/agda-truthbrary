\begin{code}
module Truthbrary.Record.Cvt where

open import Level
  as Level
  using (
    Level
  )
open import Function
  using (
    _$_
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Integer
  as ℤ
  using (
    ℤ
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )

record Cvt {a b} (A : Set a) (B : A → Set b) : Set (Level.suc a Level.⊔ b) where
  field
    mpt : A → Set a
    cnino : (x : A) → mpt x → B x

instance
  ℕ→ℤ : Cvt ℕ $ λ _ → ℤ
  ℕ→ℤ = record {
    mpt = λ _ → ⊤;
    cnino = λ n _ → ℤ.+_ n
    }

  ℤ→ℕ : Cvt ℤ $ λ _ → ℕ
  ℤ→ℕ = {!!}

  Id : ∀ {a} → {A : Set a} → Cvt A $ λ _ → A
  Id = record {
    mpt = λ _ → ⊤;
    cnino = λ x _ → x
    }
\end{code}
