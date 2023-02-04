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
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Record.SR}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o sa'u ko'a goi la'o zoi.\ \texttt\cmene .zoi.\ vasru zo'e poi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ kei je lo nu lo ctaipe be la'oi .\F{String}.\ cu binxo pe'a ru'e

.i sa'u nai ru'e vasru\ldots
\begin{itemize}
	\item vu'oi la'oi .\F{Show}.\ je la'oi .\F{show}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Show}.\ vu'o noi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ ku'o je
        \item vu'oi la'oi .\F{Read}.\ je la'oi .\F{readmaybe}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Read}.\ vu'o noi tu'a ke'a filri'a lo nu lo me'oi .\F{Maybe}.\ ctaipe cu selbi'o pe'a ru'e lo ctaipe be la'oi .\F{String}.
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.SR where

open import Data.Fin
open import Data.Nat
open import Data.Sum
open import Function
open import Data.Bool
open import Data.Char
  using (
    Char;
    fromℕ
  )
open import Data.List
  using (
    List;
    _∷_
  )
open import Data.Maybe
open import Data.String
  hiding (
    show;
    _++_
  )
open import Data.Fin.Show
  using (
  )
open import Data.Nat.Show
  using (
  )
open import Truthbrary.Record.LLC
  hiding (
    _∷_
  )
open import Relation.Binary.PropositionalEquality
\end{code}

\section{la'oi .\F{Show}.}
ni'o ga naja la'o zoi.\ \B S .zoi.\ fa'u la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \F{Show} \B A .zoi.\ fa'u la'o zoi.\ \B A .zoi.\ gi la'o zoi.\ \F{Show.show} \B S \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.

\begin{code}
record Show {a} (A : Set a) : Set a
  where
  field
    show : A → String
\end{code}

\subsection{la'oi .\F{show}.}
ni'o ga naja la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B A .zoi.\ gi la'o zoi.\ \F{show} \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.

\begin{code}
show : ∀ {a} → {A : Set a} → ⦃ Show A ⦄
     → A → String
show ⦃ boob ⦄ = Show.show boob
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  showℕ = record {show = Data.Nat.Show.show}
  showFin : {n : ℕ} → Show $ Fin n
  showFin = record {show = Data.Fin.Show.show}
  showChar = record {show = Data.Char.show}
  showString = record {show = Data.String.show}
  showMaybe : ∀ {a} → {A : Set a}
            → ⦃ Show A ⦄
            → Show $ Maybe A
  showMaybe {_} {A} = record {show = funk}
    where
    funk : Maybe A → String
    funk nothing = "nothing"
    funk (just t) = "just " ++ parens (show t)
  showSum : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Show A ⦄ → ⦃ Show B ⦄
          → Show $ A ⊎ B
  showSum {_} {_} {A} {B} = record {show = stank}
    where
    stank : A ⊎ B → String
    stank (inj₁ pa) = "inj₁ " ++ parens (show pa)
    stank (inj₂ re) = "inj₂ " ++ parens (show re)
\end{code}

\section{la'oi .\F{Read}.}
\newcommand\rmvvc{ga jonai ga je lo te samrkompli ja zo'e cu djuno lo du'u la'o zoi. \B b .zoi.\ sinxa ma kau gi ko'a goi la'o zoi.\ \F{Read.readMaybe} \F Q \B b .zoi.\ me'oi .\F{just}.\ lo selsni be la'o zoi.\ \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.}
ni'o ga jo ga je la'o zoi.\ \B Q .zoi.\ ctaipe la'o zoi.\ \F{Read} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B a .zoi.\ gi \rmvvc

\begin{code}
record Read {a} (A : Set a) : Set a
  where
  field
    readMaybe : String → Maybe A
\end{code}

\subsection{la'oi .\F{readMaybe}.}
ni'o \rmvvc

\begin{code}
readMaybe : ∀ {a} → {A : Set a} → ⦃ Read A ⦄
          → String → Maybe A
readMaybe ⦃ drivel ⦄ = Read.readMaybe drivel
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  -- | .i pilno li pano ki'u le nu pruce le te pruce
  -- be le me'oi .show. co'e pe la'oi .ℕ.
  readℕ = record {readMaybe = Data.Nat.Show.readMaybe 10}
  -- | .i pilno li pano ki'u le nu pruce le te pruce
  -- be le me'oi .show. co'e pe la'oi .Fin.
  readFin : {n : ℕ} → Read $ Fin n
  readFin = record {readMaybe = Data.Fin.Show.readMaybe 10}
\end{code}

\section{la'oi .\F{SR}.}
ni'o ga jo zasti fa lo ctaipe be la'o zoi.\ \F{SR} \B Q .zoi.\ gi ga naja la'o zoi.\ \B q .zoi.\ ctaipe la'o zoi.\ \B Q .zoi.\ gi la'o zoi.\ \F{readMaybe} \Sym\$ \F{show} \B q .zoi.\ du la'o zoi.\ \F{just} \B q .zoi.

\subsection{le cmene be le me'oi .\AgdaKeyword{field}.}
ni'o la .varik.\ cu xamsku zo'oi .\F{fat}.\ noi ke'a me'oi .\AgdaKeyword{field}.\ je ku'i cu na mutce le ka ce'u .anci\ldots kei je ku'i cu sorpa'a lo nu lo tcidu cu jimpe fi le se xamsku

\begin{code}
record SR {a} (A : Set a) ⦃ Q : Read A ⦄ ⦃ R : Show A ⦄ : Set a
  where
  field
    fat : just ≡ Read.readMaybe Q ∘ Show.show R
\end{code}
\end{document}
