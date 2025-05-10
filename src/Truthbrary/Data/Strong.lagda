\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}
\end{code}

\begin{code}
module Truthbrary.Data.Strong where
\end{code}

\begin{code}
open import Data.List
  as 𝕃
  using (
    List
  )
open import Data.Char
  using (
    Char
  )
\end{code}

\begin{code}
Strong : Set
Strong = List Char
\end{code}
