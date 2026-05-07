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

\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
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

open import Level
  using (
    _⊔_;
    suc
  )
open import Data.Fin
  using (
    Fin
  )
open import Function
  using (
    _$_
  )
  renaming (
    flip to _⍨
  )
open import Data.List
  as 𝕃
  using (
    length;
    _∷ʳ_;
    List
  )
open import Data.Product
  using (
    _×_;
    Σ
  )
open import Relation.Binary.PropositionalEquality
  using (
    cong;
    refl;
    sym;
    _≡_
  )

coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
coerce refl x = x
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
ni'o ga jo ctaipe la'o zoi.\ \F{Subtable} \B a \B b\ .zoi.\ gi lo'i ro co'e ja selvau be la'oi .\B a.\ cu klesi lo'i ro co'e ja selvau be la'oi .\B b.

\begin{code}
Subtable : ∀ {a} → Table a → Table a → Set a
Subtable = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module SubtableVeritas where
  ex : ∀ {a}
     → (x z : Table a)
     → Subtable x z
     → (d : Table.SCᵣ x ≡ Table.SCᵣ z)
     → (i : Fin $ length $ Table.r x)
     → (Σ
         (Fin _)
         (λ j →
           (_≡_
             (𝕃.lookup (Table.r x) i)
             (coerce
               (sym d)
               (𝕃.lookup (Table.r z) j)))))
  ex = {!!}

  rfl : ∀ {a} → {A : Set a} → (t : Table a) → Subtable t t
  rfl = {!!}
\end{code}

\section{la'oi .\F{SCD}.}
ni'o ga jo ctaipe la'o zoi.\ \F{SCD} \B a\ \B b\ .zoi.\ gi la'oi .\B a.\ dunli la'oi .\B b.\ le ka mu'oi zoi.\ \AgdaField{Table.SCᵣ}\ .zoi.\ ke'a kei je le ka mu'oi zoi.\ \AgdaField{Table.tcek}\ .zoi.\ ce'u

.i racli fa lo nu sruma zo'e ja le du'u zoi zoi.\ \F{SCD}\ .zoi.\ cmavlaka'i lu se ctaipe dunli li'u

\begin{code}
record SCD {a} (t₁ t₂ : Table a) : Set (suc a) where
  _⇔_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  _⇔_ A B = (A → B) × (B → A)
  field
    dscr : Table.SCᵣ t₁ ≡ Table.SCᵣ t₂
    dtck : (l : List $ Table.SCᵣ t₁)
         → let l' = _⍨ coerce l $ cong List dscr in
           Table.tcek t₁ l ⇔ Table.tcek t₂ l'
\end{code}

\section{la \F{jmina}}
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

  subtable : ∀ {a}
           → (t : Table a)
           → (r : Table.SCᵣ t)
           → (g : Table.tcek t $ Table.r t ∷ʳ r)
           → Subtable t $ jmina t r g
  subtable = {!!}
\end{code}

\section{la \F{vimcu}}

\begin{code}
vimcu : ∀ {a}
      → (t : Table a)
      → (r : Table.SCᵣ t)
      → Table.tcek t {!!}
      → Table a
vimcu = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module vimcuVeritas where
  subtable : ∀ {a}
           → (t : Table a)
           → (r : Table.SCᵣ t)
           → (T : Table.tcek t _)
           → Subtable (vimcu t r T) t
  subtable = {!!}
\end{code}

\section{ko'a goi la'oi .\AgdaRecord{Database}.}
ni'o ro da poi ke'a ctaipe ko'a zo'u da sinxa lo su'o me'oi .database.

\begin{code}
record Database {a p} : Set (Agda.Primitive.lsuc a Agda.Primitive.⊔ Agda.Primitive.lsuc p) where
  field
    tb : List $ Table a
    tcek : List $ Table a → Set p
    ctaipe : tcek tb
\end{code}
\end{document}
