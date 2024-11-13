% vdid: GVXo4Lhvc9e7jXu2
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
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\Colon}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵣ}{\ensuremath{\mathnormal{_\AgdaFontStyle{r}}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\kulmodis{\AgdaModule{Truthbrary.Record.RDB}}

\title{la'o zoi.\ \kulmodis\ .zoi.}
\author{la .varik.\ .VALefor.}

\newcommand\ckinas[1]{ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi #1\ bau la .lojban.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru zo'e je le velcki be la'oi .\AgdaRecord{Table}.

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Truthbrary.Record.RDB where

open import Function
  using (
    _$_
  )
open import Data.List
  using (
    _∷ʳ_;
    List
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    _≡_
  )
\end{code}

\section{la'oi .\AgdaRecord{Table}.}
ni'o la'oi .\AgdaRecord{Table}.\ se ctaipe lo ro me'oi .database.\ me'oi .table.

\begin{code}
record Table a : Set (Agda.Primitive.lsuc a)
  where
  field
    SCᵣ : Set a
    r : List SCᵣ
    tcek : List SCᵣ → Set a
    ctaipe : tcek r
\end{code}

\section{la'oi .\F{Subtable}.}

\begin{code}
Subtable : ∀ {a} → Table a → Table a → Set a
Subtable = {!!}
\end{code}

\section{la'oi .\F{jmina}.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
jmina : ∀ {a}
      → (t : Table a)
      → (r : Table.SCᵣ t)
      → Table.tcek t $ Table.r t ∷ʳ r
      → Table a
jmina t _ c = record t {r = _; ctaipe = c}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module jminaVeritas where
  kk : ∀ {a}
     → (t : Table a)
     → (r : Table.SCᵣ t)
     → (g : Table.tcek t $ Table.r t ∷ʳ r)
     → Table.r (jmina t r g) ≡ Table.r t ∷ʳ r
  kk _ _ _ = refl
\end{code}

\section{la'oi .\F{vimcu}.}

\begin{code}
vimcu : ∀ {a}
      → (t : Table a)
      → (r : Table.SCᵣ t)
      → (Table.tcek t {!!})
      → Table a
vimcu = {!!}
\end{code}
\end{document}
