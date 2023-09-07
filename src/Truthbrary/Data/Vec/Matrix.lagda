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
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∷}{\ensuremath{\Colon}}
\newunicodechar{∋}{\ensuremath{\ni}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Data.Vec.Matrix}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\section{le torveki}
ni'o la'o zoi.\ \texttt{\cmene} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be la'o zoi.\ \F 𝕄 .zoi.\ noi tu'a ke'a filri'a tu'a lo nacmeimei be'o je
	\item le velcki be la'o zoi.\ \F{lookup} .zoi.\ noi tu'a ke'a filri'a tu'a lo pinpau ja co'e be lo nacmeimei ku'o be'o je
	\item le velcki be la'o zoi.\ \F I .zoi.\ noi tu'a ke'a filri'a tu'a lo me'oi .identity.\ nacmeimei be'o je
	\item le velcki be la'o zoi.\ \F{\_∣\_}\ .zoi.\ noi tu'a ke'a filri'a tu'a lo konkatena bei lo ctaipe be ko'a goi la'o zoi.\ \F 𝕄\ .zoi.\ be'o bei lo ctaipe be ko'a
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
    ℕ;
    _+_
  )
open import Data.Vec
  renaming (
    lookup to lookupᵥ
  )
open import Function
\end{code}

\section{la'o zoi. \F 𝕄\ .zoi.}
ni'o ro da zo'u ga jo da ctaipe la'o zoi.\ \F 𝕄 \B A \B c \B b .zoi.\ gi da nacmeimei la'o zoi.\ \B b .zoi.\ la'o zoi.\ \B c .zoi.\ je cu vasru lo ctaipe be la'o zoi.\ \B A .zoi.

\subsection{le su'u me'oi .order.}
ni'o la'o zoi.\ \F 𝕄 \F ℕ 3 3 \F ∋ \Sym(\Sym(1 \F ∷ 2 \F \F ∷ 3 \F ∷ \AgdaInductiveConstructor{[]}\Sym) \F ∷ \Sym(4 \F ∷ 5 \F ∷ 6 \F ∷ \AgdaInductiveConstructor{[]}\Sym) \F ∷ \Sym(7 \F ∷ 8 \F ∷ 9 \F ∷ \AgdaInductiveConstructor{[]}\Sym) \F ∷ \AgdaInductiveConstructor{[]}\Sym) .zoi.\ nacmeimei je cu du la'o cmaci.
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
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{lookup}.\ bau la .lojban.

\begin{code}
lookup : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
lookup m n = map (flip lookupᵥ n) m
\end{code}

\section{la'oi .\F I.}
ni'o ga jo la'o zoi.\ \F I \B z \B o .zoi.\ me'oi .identity.\ nacmeimei gi ga je la'o zoi.\ \B z .zoi.\ du li no ja zo'e gi la'o zoi.\ \B o .zoi.\ du li pa ja zo'e

\begin{code}
I : ∀ {a} → {A : Set a} → {n : ℕ} → A → A → 𝕄 A n n
I z o = map f $ allFin _
  where
  f = λ x → updateAt x (const o) $ replicate z
\end{code}

\section{la'o zoi.\ \F{\_∣\_}\ .zoi.}
ni'o la'o zoi.\ \B a \F{∣} \B b .zoi.\ konkatena la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_∣_ : ∀ {a} → {A : Set a} → {m n o : ℕ}
    → 𝕄 A m n → 𝕄 A o n → 𝕄 A (m + o) n
_∣_ a b = map (λ n → lookupᵥ a n ++ lookupᵥ b n) $ allFin _
\end{code}
\end{document}
