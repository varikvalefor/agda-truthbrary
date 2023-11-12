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
\newunicodechar{ℤ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{∘}{\ensuremath{\circ}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^l}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^r}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^l}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^r}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{′}{\ensuremath{\mathnormal{\prime}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\Colon}}}

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
import Data.Sum.Properties
import Data.Maybe.Properties
import Data.These.Properties
import Data.Product.Properties

open import Data.Sum
open import Function
open import Data.Bool
  using (
    Bool
  )
open import Data.Maybe
open import Data.These
  using (
    These
  )
open import Data.Integer
  using (
    ℤ
  )
open import Data.Product
open import Data.Rational
  using (
    ℚ
  )
open import Data.List
  using (
    List;
    _∷_
  )
open import Data.Vec
  using (
    Vec
  )
  renaming (
    _∷_ to _∷ᵥ_;
    [] to []ᵥ
  )
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

import Data.Vec.Properties as DVP
import Data.List.Properties as DLP
\end{code}

\section{la'oi .\F{Eq}.}
\newcommand\eqq[1]{ga jonai ga je la'o zoi.\ \B a .zoi.\ du la'o zoi.\ \B b .zoi.\ gi ko'a goi la'o zoi.\ \F{isYes} \Sym \$ {#1} .zoi.\ du la'oi .\F{true}.\ gi ko'a du la'o zoi.\ \F{false} .zoi.}
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
  EqBool : Eq Bool
  EqBool = record {_≟_ = Data.Bool._≟_}
  -- | All I've got with me is a pistol and an...
  EqProd : ∀ {a b} → {A : Set a} → {B : Set b}
         → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
         → Eq $ A × B
  EqProd = record {_≟_ = Data.Product.Properties.≡-dec _≟_ _≟_}
  EqString : Eq Data.String.String
  EqString = record {_≟_ = Data.String._≟_}
  EqChar : Eq Data.Char.Char
  EqChar = record {_≟_ = Data.Char._≟_}
  EqFloat : Eq Data.Float.Float
  EqFloat = record {_≟_ = Data.Float._≟_}
  EqFin : {n : Data.Nat.ℕ} → Eq $ Data.Fin.Fin n
  EqFin = record {_≟_ = Data.Fin._≟_}
  EqMaybe : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Eq $ Maybe A
  EqMaybe = record {_≟_ = Data.Maybe.Properties.≡-dec _≟_}
  EqThese : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
          → Eq $ These A B
  EqThese = record {_≟_ = Data.These.Properties.≡-dec _≟_ _≟_}
  EqList : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Eq $ List A
  EqList = record {_≟_ = DLP.≡-dec _≟_}
  EqVec : ∀ {a} → {A : Set a} → {n : Data.Nat.ℕ} → ⦃ Eq A ⦄
        → Eq $ Vec A n
  EqVec = record {_≟_ = DVP.≡-dec _≟_}
  EqSum : ∀ {a b} → {A : Set a} → {B : Set b}
        → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
        → Eq $ A ⊎ B
  EqSum = record {_≟_ = Data.Sum.Properties.≡-dec _≟_ _≟_}
\end{code}
\end{document}
