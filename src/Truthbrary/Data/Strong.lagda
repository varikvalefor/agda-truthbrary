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

String : Set
String = List Char
\end{code}
