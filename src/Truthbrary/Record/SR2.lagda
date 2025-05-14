\begin{code}
module Truthbrary.Record.SR2 where

open import Level
  using (
    _⊔_;
    suc
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )

record Read {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    P : Strong → Set p
    read : (x : Strong) → P x → A
\end{code}
