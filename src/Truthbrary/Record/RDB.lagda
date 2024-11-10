\begin{code}
module Truthbrary.Record.RDB where

open import Function
  using (
    _$_
  )
open import Data.List
  using (
    _∷ʳ_;
    List
  )
open import Data.String
  using (
    String
  )

record Table a : Set (Agda.Primitive.lsuc a)
  where
  field
    SCᵣ : Set a
    r : List SCᵣ
    guuar : List SCᵣ → Set a
    ctaipe : guuar r

jmina : ∀ {a}
      → (t : Table a)
      → (r : Table.SCᵣ t)
      → Table.guuar t $ Table.r t ∷ʳ r
      → Table a
jmina t r c = record t {r = Table.r t ∷ʳ r; ctaipe = c}
\end{code}
