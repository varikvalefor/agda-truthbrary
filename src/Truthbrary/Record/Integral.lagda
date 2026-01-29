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
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{∃}{\ensuremath{\mathnormal{\exists}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⇒}{\ensuremath{\mathnormal{\Rightarrow}}}
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
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∣}{\ensuremath{\mathnormal|}}

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
ni'o la'o zoi.\ \texttt{Truthbrary.Record.Integral} .zoi.\ vasru ga je\ldots
\begin{itemize}
	\item le velcki be ko'a goi la'oi .\AgdaRecord{Integral}.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je cu jai filri'a tu'a lo kacna'u co'e gi
	\item le velcki be le me'oi .instance.\ be ko'a
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
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Function
  using (
    _$_;
    _∘_
  )
open import Data.Unit
  using (
    ⊤
  )
open import Data.Integer
  as ℤ
  using (
    0ℤ;
    ℤ
  )
open import Data.Product
  as Σ
  using (
    _×_
  )
open import Data.Fin.Properties
  as DFP
  using (
    toℕ-fromℕ<
  )
open import Data.Integer.Properties
  as ℤP
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    cong;
    _≡_;
    sym
  )
\end{code}

\section{la'oi .\AgdaRecord{Integral}.}
ni'o la'oi .\AgdaRecord{Integral}.\ jai filri'a tu'a lo kacna'u co'e

.i ga jo la'oi .\B k.\ ctaipe la'o zoi.\ \AgdaRecord{Integral} \B A .zoi.\ je cu ba'e drani gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{Integral.fromℤ} \B k \B z \B p\ .zoi.\ namcu du la'o zoi.\ \B z\ .zoi.\ gi
	\item ga je la'o zoi.\ \AgdaField{Integral.P} \B k .zoi.\ co'e gi
	\item ga je la'o zoi.\ \AgdaField{Integral.toℤ} \B k \B x\ .zoi.\ namcu du la'o zoi.\ \B x\ .zoi.\ gi
        \item la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi tu'a la'o zoi.\ \AgdaField{Integral.toℤ∘fromℤ} \B k\ .zoi.\ ja la'o zoi.\ \AgdaField{Integral.f≗f}\ \B k\ .zoi.\ fo lo lojbo
\end{itemize}

\begin{code}
record Integral {a p} (A : Set a) : Set (suc p Level.⊔ a)
  where
  field
    P : ℤ → Set p
    toℤ : A → ℤ
    fromℤ : (z : ℤ) → P z → A
    toℤ∘fromℤ : (z : ℤ) → (p : P z) → z ≡ toℤ (fromℤ z p)
    f≗f : (z : ℤ) → (p₁ p₂ : P z) → fromℤ z p₁ ≡ fromℤ z p₂
\end{code}

\section{le'i me'oi .instance.}

\begin{code}
instance
  _ : Integral ℤ
  _ = record {
    P = λ x → ⊤;
    fromℤ = λ x _ → x;
    toℤ∘fromℤ = λ _ _ → _≡_.refl;
    f≗f = λ _ _ _ → _≡_.refl
    }

  _ : Integral ℕ
  _ = record {
    P = λ z → z ≡ ℤ.+ ℤ.∣ z ∣;
    toℤ = ℤ.+_;
    fromℤ = λ z refl → ℤ.∣ z ∣;
    toℤ∘fromℤ = λ _ d → d;
    f≗f = λ _ _ _ → _≡_.refl
    }

  IntegralFin : {n : ℕ} → Integral $ Fin n
  IntegralFin {n} = record {
    P = λ z → (z ℤ.≥ 0ℤ) × (ℤ.∣ z ∣ ℕ.< n );
    toℤ = ℤ.+_ ∘ 𝔽.toℕ;
    fromℤ = λ _ → 𝔽.fromℕ< ∘ Σ.proj₂;
    toℤ∘fromℤ = λ z p → sym $ begin
      ℤ.+ (𝔽.toℕ $ 𝔽.fromℕ< $ Σ.proj₂ p) ≡⟨ _≡_.refl ⟩
      _ ≡⟨ cong ℤ.+_ (toℕ-fromℕ< $ Σ.proj₂ p) ⟩
      ℤ.+ ℤ.∣ z ∣ ≡⟨ ℤP.0≤n⇒+∣n∣≡n $ Σ.proj₁ p ⟩
      z ∎;
    f≗f = λ _ p₁ p₂ → DFP.fromℕ<-cong _ _ _≡_.refl (Σ.proj₂ p₁) $ Σ.proj₂ p₂
    }
    where
    open ≡-Reasoning
\end{code}
\end{document}
