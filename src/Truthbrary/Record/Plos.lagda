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

record Plos₁ {a b}
             (A B : Set a)
             (C : A → B → Set b) :
             Set (a ⊔ b) where
  field
    _+_ : (x : A) (z : B) → C x z
    ⍨! : (x : A) (z : B) → {!!}

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
