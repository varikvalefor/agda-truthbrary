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
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\hashish{cbf1 42fe 1ebd b0b2 87a4 4018 340b 8159 7ef1 3a63 6f5d 76f4 6f48 a080 b2bc d3f1 3922 f0f1 5219 94cc 5e71 fb1f b2d9 d9f8 dd3b ffe6 be32 0056 5cca 21c4 28eb 9de1}

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
	\item le velcki be la'o zoi.\ \B 𝕄 .zoi.\ noi tu'a ke'a filri'a tu'a lo nacmeimei ku'o je
        \item le velcki be la'o zoi.\ \F{\_𝕄!!\_} .zoi.\ noi tu'a ke'a filri'a tu'a lo pinpau ja co'e be lo nacmeimei ku'o je
        \item le velcki be la'o zoi.\ \F I .zoi.\ noi tu'a ke'a filri'a tu'a lo me'oi .identity.\ nacmeimei
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.Vec.Matrix where

open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Function
\end{code}

\section{la'oi .\D 𝕄.}
ni'o ro da poi ke'a mu'oi zoi.\ .\D 𝕄 \B a \B b .zoi.\ zo'u da nacmeimei la'oi .\B a.\ la'oi .\B b.

\subsection{le me'oi .field.\ pe'a ru'e}
ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo pa moi me'oi .field.\ pe'a ru'e be da cu se ctaipe lo selvau be da

ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo re moi me'oi .field.\ pe'a ru'e be da cu ni da ganra

ni'o ro da poi ke'a me'oi .\D 𝕄.\ zo'u lo ci moi me'oi .field.\ pe'a ru'e be da cu ni da rajycla

\begin{code}
𝕄 : ∀ {a} → Set a → ℕ → ℕ → Set a
𝕄 = Vec ∘₂ Vec
\end{code}

\section{la'oi .\Sym{𝕄!!}.}
ni'o la .varik.\ cu jinvi le du'u le mu'oi glibau.\ type signature .glibau.\ cu xamgu velcki

\begin{code}
_𝕄!!_ : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
_𝕄!!_ m n = map (flip lookup n) m
\end{code}

\section{la'oi .\F I.}

ni'o la'o zoi.\ \F I \{\B x\} .zoi.\ me'oi .identity.\ nacmeimei

\begin{code}
I : {n : ℕ} → 𝕄 (Fin 2) n n
I = map f $ allFin _
  where
  f = λ x → updateAt x (const $ suc zero) $ replicate zero
\end{code}
\end{document}
