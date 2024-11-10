\begin{code}
{-# OPTIONS --safe #-}

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
\end{code}

\begin{code}
record Table a : Set (Agda.Primitive.lsuc a)
  where
  field
    SCᵣ : Set a
    r : List SCᵣ
    guuar : List SCᵣ → Set a
    ctaipe : guuar r
\end{code}

\begin{code}
jmina : ∀ {a}
      → (t : Table a)
      → (r : Table.SCᵣ t)
      → Table.guuar t $ Table.r t ∷ʳ r
      → Table a
jmina t r c = record t {r = _; ctaipe = c}
\end{code}
