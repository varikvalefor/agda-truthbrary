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
    _≡_
  )

record _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    f₁ : A → B
    f₂ : B → A
    d₁ : (x : A) → x ≡ f₂ (f₁ x)
    d₂ : (x : B) → x ≡ f₁ (f₂ x)

_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ M ⦄ = _⍨M.f₁ M

instance
  ⍨-⍨ : ∀ {a b} → {A : Set a} → {B : Set b}
     → ⦃ _⍨M A B ⦄
     → _⍨M B A
  ⍨-⍨ ⦃ M ⦄ = record {
    f₁ = _⍨M.f₂ M;
    f₂ = _⍨M.f₁ M;
    d₁ = _⍨M.d₂ M;
    d₂ = _⍨M.d₁ M
    }

  ⍨-flip : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → _⍨M (A → B → C) (B → A → C)
  ⍨-flip = record {
    f₁ = flip;
    f₂ = flip;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-× : ∀ {a b} → {A : Set a} → {B : Set b}
      → _⍨M (A × B) $ B × A
  ⍨-× = record {
    f₁ = Data.Product.swap;
    f₂ = Data.Product.swap;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

open import Data.Nat

x : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
  → (A → B → C)
  → (B → A → C)
x = _⍨
\end{code}
