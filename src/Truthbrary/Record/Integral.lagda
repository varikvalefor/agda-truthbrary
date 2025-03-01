\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{∃}{\ensuremath{\mathnormal{\exists}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{ⁿ}{\ensuremath{\mathnormal{^n}}}
\newunicodechar{ʸ}{\ensuremath{\mathnormal{^y}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∉}{\ensuremath{\mathnormal{\notin}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{la'o zoi.\ \texttt{Truthbrary.Record.Integral} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{Truthbrary.Record.Integral} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be la'o zoi.\ \AgdaRecord{Integral} .zoi.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je cu jai filri'a tu'a lo kacna'u co'e
\end{itemize}

\section{le me'oi .preamble.}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.Integral where

open import Level
  using (
    zero;
    suc
  )
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    _∘_
  )
open import Data.Integer
  as ℤ
  using (
    ℤ
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )
\end{code}

\section{la'oi .\AgdaRecord{Integral}.}
ni'o la'oi .\AgdaRecord{Integral}.\ jai filri'a tu'a lo kacna'u co'e

.i ga jo la'oi .\B k.\ ctaipe la'o zoi.\ \AgdaRecord{Integral} \B A .zoi.\ je cu ba'e drani gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{Integral.fromℤ} \B k \B z \B p\ .zoi.\ namcu du la'o zoi.\ \B z\ .zoi.\ gi
	\item ga je la'o zoi.\ \AgdaField{Integral.P} \B k .zoi.\ co'e gi
	\item la'o zoi.\ \AgdaField{Integral.toℤ} \B k \B x\ .zoi.\ namcu du la'o zoi.\ \B x\ .zoi.
\end{itemize}

\begin{code}
record Integral {a p} (A : Set a) : Set (suc p Level.⊔ a)
  where
  field
    P : ℤ → Set p
    toℤ : A → ℤ
    fromℤ : (z : ℤ) → P z → A
    toℤ∘fromℤ : (z : ℤ) → (p : P z) → z ≡ toℤ (fromℤ z p)
\end{code}

\section{le'i me'oi .instance.}

\begin{code}
instance
  _ : Integral ℤ
  _ = record {
    P = λ x → x ≡ x;
    fromℤ = λ x d → x;
    toℤ∘fromℤ = λ x d → _≡_.refl
    }

  _ : Integral ℕ
  _ = record {
    P = λ z → z ℤ.≥ ℤ.0ℤ;
    toℤ = ℤ.+_;
    fromℤ = {!!};
    toℤ∘fromℤ = {!!}
    }

  _ : {n : ℕ} → Integral {p = {!!}} (Fin n)
  _ = record {
    P = {!!};
    toℤ = ℤ.+_ ∘ Data.Fin.toℕ;
    fromℤ = {!!};
    toℤ∘fromℤ = {!!}
    }
\end{code}
\end{document}
