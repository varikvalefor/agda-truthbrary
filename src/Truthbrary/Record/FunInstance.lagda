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

data _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  iso⍨ : Iso A B → _⍨M A B
  fancu⍨ : (A → B) → _⍨M A B

_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ iso⍨ M ⦄ = Iso.f₁ M
_⍨ ⦃ fancu⍨ M ⦄ = M

instance
  ⍨-⍨ : ∀ {a b} → {A : Set a} → {B : Set b}
     → ⦃ Iso A B ⦄
     → _⍨M B A
  ⍨-⍨ ⦃ M ⦄ = iso⍨ $ record {
    f₁ = Iso.f₂ M;
    f₂ = Iso.f₁ M;
    d₁ = Iso.d₂ M;
    d₂ = Iso.d₁ M
    }

  ⍨-flip : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → _⍨M (A → B → C) (B → A → C)
  ⍨-flip = iso⍨ $ record {
    f₁ = flip;
    f₂ = flip;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-× : ∀ {a b} → {A : Set a} → {B : Set b}
      → _⍨M (A × B) $ B × A
  ⍨-× = iso⍨ $ record {
    f₁ = Data.Product.swap;
    f₂ = Data.Product.swap;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-≡ : ∀ {a} → {A B : Set a} → _⍨M (A ≡ B) $ B ≡ A
  ⍨-≡ = iso⍨ $ record {
    f₁ = sym;
    f₂ = sym;
    d₁ = λ {refl → refl};
    d₂ = λ {refl → refl}
    }

  ⍨-f₁ : ∀ {a} → {A : Set a} → {B : Set a} → _⍨M (A → A → B) (A → B)
  ⍨-f₁ = fancu⍨ $ λ f x → f x x
\end{code}
