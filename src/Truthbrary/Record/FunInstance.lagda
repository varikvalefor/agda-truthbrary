\documentclass{article}

\usepackage{ar}
\usepackage{xurl}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{⍨}{\ensuremath{\raisebox{-0.25ex}{\ddot\sim}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\algoritma\textsc

\newcommand\xactaipes[1]{\textsc{#1}}

\title{la'o zoi.\ \AgdaModule{Truthbrary.Record.FunInstance}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\section{le vrici}

\begin{code}
{-# OPTIONS --backtracking-instance-search #-}
{-# OPTIONS --instance-search-depth=1 #-}
{-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --safe #-}
\end{code}

\begin{code}
module Truthbrary.Record.FunInstance where
\end{code}

\begin{code}
open import Level
  using (
    _⊔_
  )
open import Function
  using (
    flip;
    _$_
  )
open import Data.Product
  as Σ
  using (
    _×_
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    sym;
    _≡_
  )
\end{code}

\section{ko'a goi la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.\ je lo jai filri'a be tu'a ri}
ni'o le ckupau cu vasru pe'a le velcki be ko'a be'o je lo velcki be lo jai filri'a be lo nu zukte tu'a ko'a\ldots kei ja lo nu la .varik.\ cu ciksi ko'a

.i la .varik.\ cu co'e ja troci lo nu ko'a jai smimlu tu'a zoi zoi.\ \(⍨\)\ .zoi.\ poi ke'a me'oi .APL.\ fancu\ldots ge'u goi ko'e\sds  .i la .varik.\ cu stidi lo nu lo prenu je ke se slabu naje ku'i ke djica be lo nu jimpe cu tcidu lo se .urli be zoi .urli.\ \url{https://aplwiki.com/wiki/Commute}\ .urli.

\subsection{la'oi .\AgdaRecord{Iso}.}
ni'o ro da zo'u ro de zo'u ga jo ctaipe lo me'oi .\AgdaRecord{Iso}.\ bei da bei de gi da tarmi joi me lo'i ctaipe ku dunli de

\begin{code}
record Iso {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    f₁ : A → B
    f₂ : B → A
    d₁ : (x : A) → x ≡ f₂ (f₁ x)
    d₂ : (x : B) → x ≡ f₁ (f₂ x)
\end{code}

\subsection{le se ctaipe pe lo du'u xu kau mapti ko'a}
ni'o la .varik.\ cu jinvi le du'u ko'e se ctaipe pluja\sds  .i zo'e joi la'e di'u cu krinu le su'u la'o zoi.\ \D{\AgdaUnderscore{}⍨M}\ .zoi.\ me'oi .\AgdaKeyword{data}.\ co'e

.i la'o zoi.\ \IC{iso⍨}\ .zoi.\ jai filri'a tu'a zoi zoi.\ \texttt{5 = 1 *⍨ 5} .zoi.\ pe la'oi .APL.\\
.i la'o zoi.\ \IC{fancu⍨}\ .zoi.\ jai filri'a tu'a zoi zoi.\ \texttt{3125 = *⍨ 5} .zoi.\ pe la'oi .APL.

\begin{code}
data _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  iso⍨ : Iso A B → _⍨M A B
  f1⍨ : (A → B) → _⍨M A B
\end{code}

\subsection{ko'a no'u la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ri ciksi ko'a fo lo te gerna be la .lojban.

\begin{code}
_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ iso⍨ M ⦄ = Iso.f₁ M
_⍨ ⦃ f1⍨ M ⦄ = M
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}
ni'o lo me'oi .\AgdaKeyword{instance}.\ cu jai filri'a lo nu lo cmalu velcki cu co'e ja se pagbu ko'a

.i le su'u me'oi .isomorphism.\ co'e cu jai krinu le su'u la .varik.\ cu ciksi zo'e poi la .varik.\ cu jinvi le du'u ke'a zmadu ko'e goi le me'oi .APL.\ fancu le ka ce'u mapti lo so'i co'e\sds  .i ku'i la .varik.\ na birti lo du'u xu kau mapti lo ro se mapti be ko'e

\begin{code}
instance
  ⍨-Iso : ∀ {a b} → {A : Set a} → {B : Set b}
        → ⦃ Iso A B ⦄
        → _⍨M B A
  ⍨-Iso ⦃ M ⦄ = iso⍨ $ record {
    f₁ = Iso.f₂ M;
    f₂ = Iso.f₁ M;
    d₁ = Iso.d₂ M;
    d₂ = Iso.d₁ M
    }

  ⍨-flip : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → _⍨M (A → B → C) (B → A → C)
  ⍨-flip = iso⍨ $ record {
    f₁ = flip;
    f₂ = flip;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-× : ∀ {a b} → {A : Set a} → {B : Set b}
      → _⍨M (A × B) $ B × A
  ⍨-× = iso⍨ $ record {
    f₁ = Σ.swap;
    f₂ = Σ.swap;
    d₁ = λ _ → refl;
    d₂ = λ _ → refl
    }

  ⍨-≡ : ∀ {a} → {A B : Set a} → _⍨M (A ≡ B) $ B ≡ A
  ⍨-≡ = iso⍨ $ record {
    f₁ = sym;
    f₂ = sym;
    d₁ = λ {refl → refl};
    d₂ = λ {refl → refl}
    }

  ⍨-f₁ : ∀ {a b} → {A : Set a} → {B : Set b}
       → _⍨M (A → A → B) (A → B)
  ⍨-f₁ = f1⍨ $ λ f x → f x x
\end{code}

\subsection{le mupli be lo ka ce'u velcki je cu co'a ja se pagbu ko'a}

\begin{code}
private module ⍨Mupli where
  open import Function
    using (
      _⟨_⟩_
    )
  open import Data.Nat
    using (
      _^_
    )

  _ : 3125 ≡ (_^_ ⍨) 5
  _ = refl

  _ : 5 ≡ (_^_ ⍨) 1 5
  _ = refl

  -- | .i zmadu fi tu'a la'oi .APL.
  -- .i ku'i la .varik. cu jinvi le du'u mleca
  -- fi le ka li'armi fa le du'u ce'u se ctaipe ciste
  -- cizra
  _ : 5 ≡_ $ 1 ⟨ _^_ ⍨ ⟩ 5
  _ = refl
\end{code}

\subsection{le ctaipe be le su'u mapti co su'u dunli}

\begin{code}
  _ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
    → (A → B → C)
    → (B → A → C)
  _ = _⍨

  _ : ∀ {a b} → {A : Set a} → {B : Set b}
    → (A → A → B)
    → A
    → B
  _ = _⍨

  module Eq {a b c} {A : Set a} {B : Set b} {C : Set c} where
    diag : (A → A → B) → A → B
    diag f x = f x x

    _ : _⍨ ≡ flip {A = A} {B} {λ _ _ → C}
    _ = refl

    _ : _⍨ ≡ diag
    _ = refl
\end{code}
\end{document}
