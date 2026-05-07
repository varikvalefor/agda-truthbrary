\begin{code}
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

record _⍨Mp {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    _⍨ : A → B

instance
  ⍨p-flip : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
          → _⍨Mp (A → B → C) (B → A → C)
  ⍨p-flip = record {
    _⍨ = flip
    }

  ⍨p-× : ∀ {a b} → {A : Set a} → {B : Set b}
       → _⍨Mp (A × B) $ B × A
  ⍨p-× = record {
    _⍨ = Data.Product.swap
    }

record _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    f₁ : _⍨Mp A B
    f₂ : _⍨Mp B A
    d₁ : (x : A) → x ≡ _⍨Mp._⍨ f₂ (_⍨Mp._⍨ f₁ x)
    d₂ : (x : B) → x ≡ _⍨Mp._⍨ f₁ (_⍨Mp._⍨ f₂ x)

_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ M ⦄ = _⍨Mp._⍨ $ _⍨M.f₁ M

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
    f₁ = ⍨p-flip;
    f₂ = ⍨p-flip;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-× : ∀ {a b} → {A : Set a} → {B : Set b}
      → _⍨M (A × B) $ B × A
  ⍨-× = record {
    f₁ = ⍨p-×;
    f₂ = ⍨p-×;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }
\end{code}
