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

\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\kulmodis{\texttt{Truthbrary.Data.Nat}}

\title{la'o zoi.\ \kulmodis\ .zoi.}
\author{la .varik.\ .VALefor.}

\newcommand\ckinas[1]{ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi #1\ bau la .lojban.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o \kulmodis\ vasru le velcki be le fancu ja co'e poi tu'a ke'a filri'a tu'a lo srana be la'o zoi.\ \F{Data.Fin.Fin} .zoi.

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.Fin where

open import Data.Fin
open import Data.Nat
  using (
    ℕ
  )
open import Relation.Binary.PropositionalEquality
\end{code}

\section{la .\F{mink}.}
ni'o la'o zoi.\ \F{toℕ} \Sym \$ \F{mink} \B f \B t\ .zoi.\ du la'o zoi.\ \F{toℕ} \B f\ .zoi.

\begin{code}
mink : {m n : ℕ} → Fin m → m ≡ n → Fin n
mink f refl = f
\end{code}

\section{la .\F{mindus.}}
\ckinas{la .\F{mindus}.}

\begin{code}
mindus : {m n : ℕ}
       → (a : Fin m)
       → (x : m ≡ n)
       → (z : n ≡ m)
       → mink (mink a x) z ≡ a
mindus a refl refl = refl
\end{code}
\end{document}