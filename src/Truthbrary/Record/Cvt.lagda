\begin{code}
module Truthbrary.Record.Cvt where

open import Level
  as Level
  using (
    Level
  )

record Cvt {a b} (A : Set a) (B : A → Set b) : Set (Level.suc a Level.⊔ b) where
  field
    mpt : A → Set a
    cnino : (x : A) → mpt x → B x
\end{code}
