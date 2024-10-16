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

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor

\newcommand\cmene{Truthbrary.Data.Vec.Matrix}

\title{la'o zoi.\ \AgdaModule{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\section{le torveki}
ni'o klesi lo'i ro co'e poi su'o da zo'u da selvau pe'a la'o zoi.\ \AgdaModule{\cmene} .zoi.\ je cu velcki ke'a ku'o fa\ldots
\begin{itemize}
	\item la'oi .\F 𝕄.\ noi ke'a jai filri'a tu'a lo nacmeimei be'o ce
	\item la'oi .\F{lookup}.\ noi tu'a ke'a filri'a tu'a lo pinpau ja co'e be lo nacmeimei ku'o be'o ce
	\item la'oi .\F I.\ noi ke'a jai filri'a tu'a lo me'oi .identity.\ nacmeimei be'o ce
	\item la'o zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.\ noi tu'a ke'a filri'a tu'a lo konkatena bei lo nacmeimei bei lo nacmeimei
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Truthbrary.Data.Vec.Matrix where

open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    _+_;
    ℕ
  )
open import Data.Vec
  using (
    replicate;
    updateAt;
    allFin;
    _++_;
    Vec;
    map
  )
  renaming (
    lookup to lookupᵥ
  )
open import Function
  using (
    const;
    _∘₂_;
    flip;
    _$_
  )
\end{code}

\section{la'oi .\F 𝕄.}
ni'o ro da zo'u ga jo da ctaipe la'o zoi.\ \F 𝕄 \B A \B c \B b .zoi.\ gi da nacmeimei la'oi .\B b.\ la'oi .\B c.\ je cu vasru pe'a lo ctaipe be la'oi .\B A.

\subsection{le su'u me'oi .order.}
\newcommand\InductiveOperator[1]{\AgdaOperator{\IC{#1}}}
\newcommand\nacmeimeiPagbu[3]{\AgdaNumber{#1} \InductiveOperator ∷ \AgdaNumber{#2} \InductiveOperator ∷ \AgdaNumber{#3} \InductiveOperator ∷ \IC{[]}}
ni'o la'o zoi.\
\F 𝕄 \D ℕ \AgdaNumber 3 \AgdaNumber 3 \AgdaOperator{\F ∋}
	\Sym(\Sym(\nacmeimeiPagbu123\Sym) \InductiveOperator ∷
	     \Sym(\nacmeimeiPagbu456\Sym) \InductiveOperator ∷
	     \Sym(\nacmeimeiPagbu789\Sym) \InductiveOperator ∷
	     \IC{[]}\Sym)
.zoi.\ nacmeimei je cu du la'e zoi cmaci.
\[
	\begin{bmatrix}
		1 & 2 & 3 \\
		4 & 5 & 6 \\
		7 & 8 & 9
	\end{bmatrix}
\]
.cmaci.

\begin{code}
𝕄 : ∀ {a} → Set a → ℕ → ℕ → Set a
𝕄 = Vec ∘₂ Vec
\end{code}

\section{la'oi .\F{lookup}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{lookup}.\ fo lo te gerna be fi la .lojban.

\begin{code}
lookup : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
lookup m n = map (flip lookupᵥ n) m
\end{code}

\section{la'oi .\F I.}
ni'o ga jo la'o zoi.\ \F I \Sym\{\AgdaUnderscore\Sym\} \Sym\{\B A\Sym\} \B z \B o .zoi.\ me'oi .identity.\ nacmeimei gi ro da poi ke'a ctaipe la'o zoi.\ \B A .zoi.\ zo'u ga je lo pilji ja co'e be da bei la'o zoi.\ \B z .zoi.\ du la'o zoi.\ \B z .zoi.\ gi da pilji ja co'e da la'o zoi.\ \B o .zoi.

\begin{code}
I : ∀ {a n} → {A : Set a} → A → A → 𝕄 A n n
I z o = map (λ x → updateAt x (const o) $ replicate z) $ allFin _
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \AgdaOperator{\F ∣} \B b .zoi.\ konkatena la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_∣_ : ∀ {a m n o} → {A : Set a}
    → 𝕄 A m n
    → 𝕄 A o n
    → 𝕄 A (m + o) n
_∣_ a b = map (λ n → lookupᵥ a n ++ lookupᵥ b n) $ allFin _
\end{code}
\end{document}
