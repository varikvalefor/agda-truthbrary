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
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\mathrm{b}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Data.List.Split}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle
\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{\cmene} .zoi.\ vasru le fancu poi tu'a ke'a filri'a lo nu lo liste cu binxo lo liste be lo'i liste

.i sa'u nai ru'e la'o zoi.\ \texttt{\cmene} .zoi.\ vasru\ldots
\begin{itemize}
	\item la'oi .\F{splitOn}.\ noi tu'a ke'a filri'a lo nu lo selvau be lo liste cu binxo pe'a ru'e lo korbi be lo liste bei lo liste
\end{itemize}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.List.Split where

open import Function
open import Data.Bool
  using (
    if_then_else_
  )
open import Data.List
  using (
    List
  )
  renaming (
    _∷_ to _∷ₗ_;
    [] to []ₗ
  )
open import Truthbrary.Record.Eq
open import Truthbrary.Record.LLC
open import Relation.Nullary.Decidable
  using (
    isYes
  )
\end{code}

\section{la'oi .\F{splitOn}.}
ni'o ga jo ko'a goi la'o zoi\ \B a .zoi.\ ctaipe la'o zoi.\ \F{List} \B A .zoi.\ gi ga je la'o zoi.\ \F{splitOn} \B a \B l .zoi.\ liste lo'i liste be lo'i ctaipe be la'o zoi.\ \B A .zoi.\ be'o poi ke'a selvau la'o zoi.\ \B a .zoi.\ gi lo du be la'o zoi.\ \B a .zoi.\ be'o pe la'o zoi.\ \B l .zoi.\ cu me'oi .correspond.\ lo korbi be ko'e goi lo selvau be ko'a be'o bei lo selvau be ko'a be'o poi ke'a na du ko'e

\begin{code}
splitOn : ∀ {a} → {A : Set a}
        → ⦃ Eq A ⦄
        → A → List A → List $ List A
splitOn a = rev ∘ map rev ∘ sob a [] []
  where
  rev = Data.List.reverse
  sob : ∀ {a} → {A : Set a}
      → ⦃ Eq A ⦄
      → A → List $ List A → List A → List A → List $ List A
  sob a b g []ₗ = g ∷ₗ b
  sob a b g (f ∷ₗ xs) = if f ≡ᵇ a then hitit else add
    where
    hitit = sob a (g ∷ₗ b) []ₗ xs
    add = sob a b (f ∷ₗ g) xs
\end{code}
\end{document}
