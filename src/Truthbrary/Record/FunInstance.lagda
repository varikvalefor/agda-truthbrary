\begin{code}
{-# OPTIONS --backtracking-instance-search #-}
module Truthbrary.Record.FunInstance where
\end{code}

\begin{code}
open import Level
  using (
    _⊔_
  )
open import Function
  using (
    flip;
    _$_
  )
open import Data.Product
  using (
    _×_
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    sym;
    _≡_
  )

record Iso {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    f₁ : A → B
    f₂ : B → A
    d₁ : (x : A) → x ≡ f₂ (f₁ x)
    d₂ : (x : B) → x ≡ f₁ (f₂ x)

_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ Iso A B ⦄ → A → B
_⍨ ⦃ M ⦄ = Iso.f₁ M

instance
  ⍨-⍨ : ∀ {a b} → {A : Set a} → {B : Set b}
     → ⦃ Iso A B ⦄
     → Iso B A
  ⍨-⍨ ⦃ M ⦄ = record {
    f₁ = Iso.f₂ M;
    f₂ = Iso.f₁ M;
    d₁ = Iso.d₂ M;
    d₂ = Iso.d₁ M
    }

  ⍨-flip : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → Iso (A → B → C) (B → A → C)
  ⍨-flip = record {
    f₁ = flip;
    f₂ = flip;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-× : ∀ {a b} → {A : Set a} → {B : Set b}
      → Iso (A × B) $ B × A
  ⍨-× = record {
    f₁ = Data.Product.swap;
    f₂ = Data.Product.swap;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-≡ : ∀ {a} → {A B : Set a} → Iso (A ≡ B) $ B ≡ A
  ⍨-≡ = record {
    f₁ = sym;
    f₂ = sym;
    d₁ = λ {refl → refl};
    d₂ = λ {refl → refl}
    }
\end{code}
