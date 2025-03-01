\begin{code}
module Truthbrary.Record.Plos where

open import Level
  using (
    _⊔_
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
       → let z' = coerce {!!} z in
         (dc : C x z ≡ C z' (coerce {!!} x))
       → (x + z) ≡ coerce (sym dc) (z' + coerce {!!} x)

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
