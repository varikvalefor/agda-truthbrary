\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\Xr[2]{\textrm{#1(#2)}}
\newcommand\datnyveicme\texttt

\title{la'o zoi.\ \datnyveicme{Truthbrary.Data.Strong}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
ni'o skicu bau la'oi .Agda.\ fe ko'a goi la'oi .\F{Strong}.\ noi ke'a smimlu ko'e goi la'o zoi.\ \AgdaPostulate{Data.String.String}\ .zoi.\ po la'o zoi.\ agda-stdlib .zoi.\ je ku'i cu zmadu fi le ka ce'u jai filri'a tu'a lo ctaipe\ldots ku'o ge'u je lo fancu pe ko'a\sds  .i troci lo nu frili fa lo nu basygau pe'a lo ctaipe pe ko'e lo ctaipe pe ko'a
\end{abstract}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
\end{code}

\begin{code}
module Truthbrary.Data.Strong where
\end{code}

\begin{code}
open import Function
  using (
    _$_;
    id
  )
open import Data.List
  as 𝕃
  using (
    List
  )
open import Data.Char
  using (
    Char
  )
open import Relation.Nullary
  using (
    yes;
    no
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Record.LLC
  using (
    _∉_
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

import Data.String as 𝕊
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
\end{code}

\section{la'oi .\F{Strong}.}
ni'o ko'a goi la'oi .\F{Strong}.\ smimlu la'o zoi.\ \AgdaPostulate{Data.String.String}\ .zoi.\ po la'o zoi.\ agda-stdlib\ .zoi.\ldots noi ku'i la .varik.\ cu tolnei tu'a lo ctaipe pe ke'a ki'u le su'u ke'a me'oi .\AgdaKeyword{postulate}.\ldots ku'o le ka ce'u ctaipe zo'e je lo se tcidu

\begin{code}
Strong : Set
Strong = List Char
\end{code}

\section{le mapti fancu}

\begin{code}
toList : Strong → List Char
toList = id
\end{code}

\begin{code}
fromList : List Char → Strong
fromList = id
\end{code}

\section{la'oi .\F{unwords}.}

\begin{code}
unwords : List Strong → Strong
unwords x = 𝕃.concat $ 𝕃.intersperse 𝕃.[ ' ' ] x
\end{code}

\section{la'oi .\F{words}.}
ni'o ga je ro da poi ke'a cmima pe'a la'o zoi.\ \F{words} \B{x}\ .zoi.\ zo'u lo no canlu lerfu cu cmima pe'a da gi la'oi .\B x.\ du la'o zoi.\ \F{concat} \OpF{\$} \F{words} \AgdaBound{x}\ .zoi.

\begin{code}
module words where
  soi : List Strong → Strong → Char → Strong → List Strong
  soi buf 𝕃.[] s 𝕃.[] = 𝕃.reverse buf
  soi buf c s 𝕃.[] = 𝕃.reverse $ c 𝕃.∷ buf
  soi buf c s (' ' 𝕃.∷ xs) = soi (c 𝕃.∷ buf) 𝕃.[] s xs
  soi buf c s (x 𝕃.∷ xs) = soi buf (c 𝕃.++ 𝕃.[ x ]) s xs

  splitOn' : Char → Strong → List Strong
  splitOn' = soi 𝕃.[] 𝕃.[]

  words : Strong → List Strong
  words = splitOn' ' '

  module Veritas where
    nocan : (x : Strong) → 𝕃.All (' ' ∉_) $ words x
    nocan = {!!}

    konk : (x : Strong) → x ≡ unwords (words x)
    konk = {!!}

words : Strong → List Strong
words = words.words
\end{code}

\section{la'oi .\F{lines}.}
ni'o ga je ro da poi ke'a cmima pe'a la'o zoi.\ \F{words} \B{x}\ .zoi.\ zo'u lo no lerpinsle bitmu lerfu lerfu cu cmima pe'a da gi la'oi .\B x.\ du la'o zoi.\ \F{𝕃.concat} \OpF{\$} \F{𝕃.intersperse} \OpF{𝕃.[} \AgdaString{"\textbackslash{}n"} \OpF{]} \OpF{\$} \F{words} \AgdaBound{x}\ .zoi.

\begin{code}
lines : Strong → List Strong
lines = words.splitOn' '\n'
\end{code}


\end{document}
