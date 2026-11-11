\begin{code}
module Truthbrary.Record.Cvt where

open import Level
  as Level
  using (
    Level
  )
open import Function
  using (
    _∘_;
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
open import Data.Product
  as Σ
  using (
    _,_;
    Σ
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

record Cvt {a b c} (A : Set a) (B : A → Set b) : Set (Level.suc a Level.⊔ Level.suc b Level.⊔ Level.suc c) where
  field
    mpt : A → Set (a Level.⊔ b Level.⊔ c)
    cnino : (x : A) → mpt x → B x

instance
  Id : ∀ {a} → {A : Set a} → Cvt {c = Level.zero} A $ λ _ → A
  Id = record {
    mpt = λ _ → ⊤;
    cnino = λ x _ → x
    }

  Comp : ∀ {a b c d} → {A : Set a} → {B : Set b} → {C : Set c}
       → {Cvt {c = d} A $ λ _ → B}
       → {Cvt {c = d} B $ λ _ → C}
       → Cvt {c = b Level.⊔ d} A $ λ _ → C
  Comp {C = _} {Cab} {Cbc} = record {
    mpt = λ x → Σ (Cvt.mpt Cab x) $ Cvt.mpt Cbc ∘ Cvt.cnino Cab x;
    cnino = λ x (z₁ , z₂) → Cvt.cnino Cbc (Cvt.cnino Cab x z₁) z₂
    }

  ℕ→ℤ : Cvt {c = Level.zero} ℕ $ λ _ → ℤ
  ℕ→ℤ = record {
    mpt = λ _ → ⊤;
    cnino = λ n _ → ℤ.+_ n
    }

  ℤ→ℕ : Cvt {c = Level.zero} ℤ $ λ _ → ℕ
  ℤ→ℕ = record {
    mpt = ℤ.0ℤ ℤ.≤_;
    cnino = {!!}
    }
\end{code}
