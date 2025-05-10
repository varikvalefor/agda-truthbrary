\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Truthbrary.Data.Strong where

open import Data.List
  as 𝕃
  using (
    List
  )
open import Data.Char
  using (
    Char
  )

Strong : Set
Strong = List Char
\end{code}
