\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb{S}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb{R}}}}
\newunicodechar{ℂ}{\ensuremath{\mathnormal{\mathbb{C}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathnormal{\mathrm{?\!?}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{σ}{\ensuremath{\mathnormal{\sigma}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathsf{m}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\mathsf{s}}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{′}{\ensuremath{\mathnormal{'}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≗}{\ensuremath{\mathnormal{\circeq}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{la'o zoi.\ \texttt{Truthbrary.Data.Mrena'u}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
\noindent
ni'o bau la .lojban.\ joi la'oi .Agda.\ la .varik.\ cu ciksi ko'a goi lo mrena'u se ctaipe ge'u je lo jai filri'a be tu'a ko'a
\end{abstract}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.Mrena'u where

open import Algebra
  using (
    Associative
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Function
  using (
    _$_
  )
open import Data.Integer
  as ℤ
  using (
    ℤ
  )
open import Data.Product
  using (
    _×_;
    _,_
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

import Level
\end{code}

\section{la'oi .\F ℝ.}
ni'o la'oi .\F ℝ.\ ctaipe lo ro mrena'u\ldots{}\ jenai zo'e  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B a \B b\ .zoi.\ poi ke'a ctaipe la'oi .\F ℝ.\ cu du lo sumji be la'oi .\B a.\ bei lo pilji be lo me'oi .sign.\ namcu be la'oi .\B a.\ be'o bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.

.i la .varik.\ cu pacna lo nu frili cumki fa lo nu xagzengau pe'a le velcki

\begin{code}
ℝ : Set
ℝ = ℤ × {!!}
\end{code}

\section{la'o zoi.\ \F{fromℕ} .zoi.}
ni'o la'o zoi.\ \F{fromℕ} \B n\ .zoi.\ namcu du la'oi .\B n.

\begin{code}
fromℕ : ℕ → ℝ
fromℕ n = ℤ.+_ n , {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}+\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF + \B b\ .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_+_ : ℝ → ℝ → ℝ
_+_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _+_Veritas where
  +≡+⍨ : Associative {ℓ = Level.zero} {!!} _+_
  +≡+⍨ = {!!}

  dratadratas : (r s : ℝ)
              → ¬_ $ r ≡ s
              → let N = λ x → ¬_ $ x ≡ r + s in
                N r × N s
  dratadratas = {!!}
\end{code}

\begin{code}
div : ℝ → (d : ℝ) → ¬_ $ d ≡ fromℕ 0 → ℝ
div = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module DivVeritas where
  sez≡1 : (r : ℝ) → (d : _) → div r r d ≡ fromℕ 1
  sez≡1 = {!!}

  r≡r/1 : (r : ℝ) → r ≡_ $ div r (fromℕ 1) {!!}
  r≡r/1 = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ zmadu la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _>_Veritas where
  ¬sez : (r : ℝ) → ¬_ $ r > r
  ¬sez = {!!}

  zmad : (r s : ℝ) → s > fromℕ 0 → (r + s) > r
  zmad = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≥\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≥ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavmau la'oi .\B b.

\begin{code}
_≥_ : ℝ → ℝ → Set
_≥_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _≥_Veritas where
  sez : (r : ℝ) → r ≥ r
  sez = {!!}

  >⇒≥ : (r s : ℝ) → r > s → r ≥ s
  >⇒≥ = {!!}
\end{code}
\end{document}
