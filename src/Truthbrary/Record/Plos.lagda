\begin{code}
module Truthbrary.Record.Plos where

open import Level
  using (
    _⊔_
  )
open import Data.Fin
  as 𝔽
  renaming (
    Fin to 𝔽
  )
  using (
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Function
  using (
    _∋_
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    sym;
    _≡_
  )

coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce refl A = A

record Plos₁ {a b}
             (A B : Set a)
             (C : A → B → Set b) :
             Set (Level.suc a ⊔ Level.suc b) where
  field
    _+_ : (x : A) (z : B) → C x z
    ⍨! : (d : A ≡ B)
       → (x : A)
       → (z : B)
       → let x' = coerce d x in
         let z' = coerce (sym d) z in
         (dc : C x z ≡ C z' x')
       → (x + z) ≡ coerce (sym dc) (z' + x')

record Plos {a b c}
            (A : Set a)
            (B : A → Set b)
            (C : (x : A) → B x → Set c) :
            Set (a ⊔ b ⊔ c) where
  field
    _+_ : (x : A) → (z : B x) → C x z
    ⍨! : (x : A) → (z : B x) → {!!}

record Min {a b c}
           (A : Set a)
           (B : A → Set b)
           (C : (x : A) → B x → Set c) :
           Set (a ⊔ b ⊔ c) where
  field
    _-_ : (x : A) → (z : B x) → C x z
\end{code}

\begin{code}
instance
  ℕ→𝔽 : {n : ℕ} → Plos ℕ (λ _ → ℕ) (λ _ _ → 𝔽 (ℕ.suc n))
  ℕ→𝔽 = record {
    _+_ = {!!};
    ⍨! = {!!}
    }

  ℕ→ℕ : Plos ℕ (λ _ → ℕ) (λ _ _ → ℕ)
  ℕ→ℕ = {!!}
\end{code}
