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

\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\kulmodis{\AgdaModule{Truthbrary.Data.Fin}}

\title{la'o zoi.\ \kulmodis\ .zoi.}
\author{la .varik.\ .VALefor.}

\newcommand\ckinas[1]{ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi #1\ bau la .lojban.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru le velcki be le co'e ja fancu poi tu'a ke'a filri'a tu'a lo srana be la'oi .\D{Fin}.

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.Fin where

open import Function
  using (
    _∘_;
    _$_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import Data.Fin
  using (
    fromℕ;
    zero;
    toℕ;
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Relation.Binary.PropositionalEquality
  using (
    cong;
    refl;
    _≗_;
    _≡_
  )
\end{code}

\section{la .\F{mink}.}
ni'o la'o zoi.\ \F{toℕ} \AgdaOperator{\AgdaFunction{\$}} \F{mink} \B f \B t\ .zoi.\ du la'o zoi.\ \F{toℕ} \B f\ .zoi.

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
       → _≡ a $ mink (mink a x) z
mindus _ refl refl = refl
\end{code}

\section{la .\F{tomindus}.}
\ckinas{la .\F{tomindus}.}

\begin{code}
tomindus : {m n : ℕ}
         → (x : Fin m)
         → (d : m ≡ n)
         → toℕ x ≡ toℕ (mink x d)
tomindus _ refl = refl
\end{code}

\section{la .\F{tondus}.}
\ckinas{la .\F{tondus}.}

\subsection{le srana be lo du'u xu kau mapti}
ni'o xu la .\F{tondus}.\ cu mapti la'o zoi.\ \kulmodis\ .zoi.  .i la .\F{tondus}.\ cu srana le fancu pe la'o zoi.\ \AgdaModule{Data.Fin}\ .zoi\ldots ge'u je ku'i zo'e pe la'o zoi.\ \AgdaModule{Data.Nat}\ .zoi.

\begin{code}
tondus : (_≗ id) (toℕ ∘ fromℕ)
tondus 0 = refl
tondus (ℕ.suc n) = tondus _ ▹ cong ℕ.suc
\end{code}

\section{la .\F{minzero}.}
\ckinas{la .\F{minzero}.}

\begin{code}
minzero : {m n : ℕ} → mink {ℕ.suc m} zero ≗ (λ _ → zero {n})
minzero refl = refl
\end{code}
\end{document}
