\begin{code}
module Truthbrary.Record.Plos where

open import Level
  using (
    _⊔_
  )
record Plos {a b c}
            (A : Set a)
            (B : A → Set b)
            (C : (x : A) → B x → Set c) :
            Set (a ⊔ b ⊔ c) where
  field
    _+_ : (x : A) → (z : B x) → C x z

record Min {a b c}
           (A : Set a)
           (B : A → Set b)
           (C : (x : A) → B x → Set c) :
           Set (a ⊔ b ⊔ c) where
  field
    _-_ : (x : A) → (z : B x) → C x z
\end{code}
