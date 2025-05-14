\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\Xr[2]{\textrm{#1(#2)}}
\newcommand\datnyveicme\texttt

\title{la'o zoi.\ \datnyveicme{Truthbrary.Record.SR2}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{code}
module Truthbrary.Record.SR2 where

open import Level
  using (
    _⊔_;
    suc
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    _⊎_
  )
open import Function
  using (
    _∘_;
    _$_
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
open import Data.Maybe
  using (
    Is-nothing;
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Data.Product
  using (
    proj₁;
    _×_;
    _,_
  )
open import Relation.Unary
  using (
    Decidable;
    _⊆_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Relation.Nullary.Decidable
  using (
    from-yes
  )
open import Data.List.Relation.Unary.All
  as 𝕃All
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

import Data.Maybe.Relation.Unary.Any
  as DMRN

module apDec where
  apDec' : ∀ {a b p}
         → {A : Set a} → {B : Set b}
         → {P : A → Set p}
         → (f : (x : A) → P x → B)
         → (x : A)
         → Dec $ P x
         → Maybe B
  apDec' f x (yes p) = just $ f x p
  apDec' _ _ _ = nothing

  apDec : ∀ {a b p}
        → {A : Set a} → {B : Set b}
        → {P : A → Set p}
        → (f : (x : A) → P x → B)
        → (P? : Decidable P)
        → A
        → Maybe B
  apDec f P? x = apDec' f x $ P? x

apDec = apDec.apDec

record Read {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    P : Strong → Set p
    read : (x : Strong) → P x → A

record ReadMaybe {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    rr : Read {p = p} A
    P? : Decidable $ Read.P rr

  open Read rr

  readMaybe = apDec read P?

  field
    justys : P ⊆ (Is-just ∘ readMaybe)
    nad : (¬_ ∘ P) ⊆ (Is-nothing ∘ readMaybe)

module readNat where
    private
      j : {m n : ℕ} → m ℕ.< n → Maybe $ Fin n
      j = just ∘ 𝔽.fromℕ<

    IsDigit : Char → Set
    toFin10 : Char → Maybe $ Fin 10
    IsDigit = Is-just ∘ toFin10
    toFin10 '0' = just 𝔽.zero
    toFin10 '1' = j $ from-yes $ 1 ℕ.<? 10
    toFin10 '2' = j $ from-yes $ 2 ℕ.<? 10
    toFin10 '3' = j $ from-yes $ 3 ℕ.<? 10
    toFin10 '4' = j $ from-yes $ 4 ℕ.<? 10
    toFin10 '5' = j $ from-yes $ 5 ℕ.<? 10
    toFin10 '6' = j $ from-yes $ 6 ℕ.<? 10
    toFin10 '7' = j $ from-yes $ 7 ℕ.<? 10
    toFin10 '8' = j $ from-yes $ 8 ℕ.<? 10
    toFin10 '9' = j $ from-yes $ 9 ℕ.<? 10
    toFin10 _ = nothing

    IsDigit? : Decidable IsDigit
    IsDigit? x with toFin10 x
    ... | just _ = yes $ DMRN.just _
    ... | nothing = no $ λ ()

    djm0 : Strong → Set
    djm0 = 𝕃All.All IsDigit

    read' : {x : Strong} → djm0 x → ℕ × ℕ
    read' 𝕃All.[] = 0 , 0
    read' (p 𝕃All.∷ ps) =
      n ℕ.+ cℕ ℕ.* 10 ℕ.^ e , ℕ.suc e
      where
      n = proj₁ $ read' ps
      e = Data.Product.proj₂ $ read' ps
      cℕ = 𝔽.toℕ $ Data.Maybe.to-witness p

instance
  readNat : Read ℕ
  readNat = record {
    read = λ x → proj₁ ∘ readNat.read' {x}
    }

  readMaybeNat : ReadMaybe ℕ
  readMaybeNat = record {
    rr = readNat;
    P? = 𝕃All.all? readNat.IsDigit?;
    justys = {!!};
    nad = {!!}}
\end{code}
\end{document}
