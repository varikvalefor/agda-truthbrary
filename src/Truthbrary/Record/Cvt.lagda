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
open import Data.Rational
  as ℚ
  using (
    ℚ
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
  Id : ∀ {a} → {A : Set a} → Cvt A $ λ _ → A
  Id = record {
    mpt = λ _ → ⊤;
    cnino = λ x _ → x
    }

  Comp : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
       → {Cvt A $ λ _ → B}
       → {Cvt B $ λ _ → C}
       → Cvt A $ λ _ → C
  Comp = record {
    mpt = {!!};
    cnino = {!!}
    }

  ℕ→ℤ : Cvt ℕ $ λ _ → ℤ
  ℕ→ℤ = record {
    mpt = λ _ → ⊤;
    cnino = λ n _ → ℤ.+_ n
    }

  ℤ→ℕ : Cvt ℤ $ λ _ → ℕ
  ℤ→ℕ = record {
    mpt = ℤ.0ℤ ℤ.≤_;
    cnino = {!!}
    }
\end{code}
