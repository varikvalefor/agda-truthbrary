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
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{′}{\ensuremath{\mathnormal{\prime}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{la'o zoi.\ \texttt{Truthbrary.Record.Eq} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{Truthbrary.Record.Eq} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be ko'a goi la'oi .\F{\_≟\_}.\ noi tu'a ke'a filri'a lo nu jdice lo jei dunli be'o je
	\item le velcki be ko'e goi le me'oi .\AgdaKeyword{record}.\ poi ke'a jicmu ko'a be'o je
	\item le me'oi .\F{instance}.\ pe ko'e
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.Eq where

import Level
import Data.Fin
import Data.Nat
import Data.Char
import Data.Float
import Data.String
open import Data.Sum
open import Function
open import Data.Bool
  using (
    Bool
  )
open import Data.Maybe
open import Data.Integer
  using (
    ℤ
  )
open import Data.Rational
  using (
    ℚ
  )
open import Relation.Nullary
open import Data.Maybe.Properties
open import Relation.Nullary.Decidable
open import Relation.Binary.Structures
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
\end{code}

\section{la'oi .\F{Eq}.}
\newcommand\eqq[1]{ga jonai ga je la'o zoi.\ \B a .zoi.\ du la'o zoi.\ \B b .zoi.\ gi ga je ko'a goi la'o zoi.\ \F{isYes} \Sym \$ {#1} .zoi.\ du la'oi .\F{true}. gi co'e gi ko'a du la'o zoi.\ \F{nothing}.}
ni'o ga jo ga je la'o zoi.\ \B Q .zoi.\ ctaipe la'o zoi.\ \F{Eq} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ je la'o zoi.\ \B b .zoi.\ ctaipe la'o zoi.\ \B A .zoi.\ gi \eqq{\F{Eq.\_≟\_} \B Q \B a \B b}

\begin{code}
record Eq {a} (A : Set a) : Set (Level.suc a)
  where
  field
    _≟_ : DecidableEquality A
\end{code}

\subsection{la'oi .\F{\_≟\_}.}
ni'o \eqq{\B a \Sym ≟ \B b}

\begin{code}
_≟_ : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → DecidableEquality A
_≟_ ⦃ Q ⦄ = Eq._≟_ Q
\end{code}

\subsection{la'oi .\F{\_≡ᵇ\_}.}

\begin{code}
_≡ᵇ_ : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → A → A → Bool
_≡ᵇ_ = isYes ∘₂ _≟_
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  Eqℕ : Eq Data.Nat.ℕ
  Eqℕ = record {_≟_ = Data.Nat._≟_}
  Eqℚ : Eq ℚ
  Eqℚ = record {_≟_ = Data.Rational._≟_}
  Eqℤ : Eq ℤ
  Eqℤ = record {_≟_ = Data.Integer._≟_}
  EqString : Eq Data.String.String
  EqString = record {_≟_ = Data.String._≟_}
  EqChar : Eq Data.Char.Char
  EqChar = record {_≟_ = Data.Char._≟_}
  EqFloat : Eq Data.Float.Float
  EqFloat = record {_≟_ = Data.Float._≟_}
  EqFin : {n : Data.Nat.ℕ} → Eq $ Data.Fin.Fin n
  EqFin = record {_≟_ = Data.Fin._≟_}
  EqMaybe : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Eq $ Maybe A
  EqMaybe {_} {A} ⦃ G ⦄ = record {_≟_ = ≡-dec $ Eq._≟_ G}
  EqSum : ∀ {a b} → {A : Set a} → {B : Set b}
        → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
        → Eq $ A ⊎ B
  EqSum {_} {_} {A} {B} = record {_≟_ = Q}
    where
    inj₁-inj : ∀ {a b} → {A : Set a} → {B : Set b} → {x y : A}
             → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
    inj₁-inj refl = refl
    inj₂-inj : ∀ {a b} → {A : Set a} → {B : Set b} → {x y : B}
             → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
    inj₂-inj refl = refl
    Q : DecidableEquality $ A ⊎ B
    Q (inj₁ t) (inj₁ l) = map′ (cong inj₁) inj₁-inj $ t ≟ l
    Q (inj₂ t) (inj₂ l) = map′ (cong inj₂) inj₂-inj $ t ≟ l
    Q (inj₁ _) (inj₂ _) = no $ λ ()
    Q (inj₂ _) (inj₁ _) = no $ λ ()
\end{code}
\end{document}
