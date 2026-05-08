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

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝕍}{\ensuremath{\mathnormal{\mathbb V}}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≅}{\ensuremath{\mathnormal\cong}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb B}}}
\newunicodechar{ν}{\ensuremath{\mathnormal\nu}}
\newunicodechar{μ}{\ensuremath{\mathnormal\mu}}
\newunicodechar{τ}{\ensuremath{\mathnormal\tau}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^\AgdaFontStyle{l}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal\geq}}
\newunicodechar{≮}{\ensuremath{\mathnormal\nless}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\phi}}
\newunicodechar{∧}{\ensuremath{\mathnormal\wedge}}
\newunicodechar{∣}{\ensuremath{\mathnormal |}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{σ}{\ensuremath{\mathnormal\sigma}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₓ}{\ensuremath{\mathnormal{_\AgdaFontStyle{x}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\AgdaFontStyle{m}}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_\AgdaFontStyle{p}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal\delta}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{↔}{\ensuremath{\mathnormal\leftrightarrow}}
\newunicodechar{≰}{\ensuremath{\mathnormal\nleq}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{⍨}{\ensuremath{\raisebox{-0.25ex}{\ddot\sim}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
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
ni'o le ckupau cu vasru pe'a le velcki be ko'a be'o je lo velcki be lo jai filri'a be lo nu pilno ko'a\ldots kei ja lo nu la .varik.\ cu ciksi ko'a

.i la .varik.\ cu co'e ja troci lo nu ko'a jai smimlu tu'a zoi zoi.\ \(⍨\)\ .zoi.\ poi ke'a me'oi .APL.\ fancu\ldots ge'u goi ko'e\sds  .i la .varik.\ cu stidi lo nu lo prenu je ke se slabu naje ku'i ke djica be lo nu jimpe cu tcidu lo se .urli be zoi .urli.\ \url{https://aplwiki.com/wiki/Commute}\ .urli.

\subsection{la'oi .\AgdaRecord{Iso}.}
ni'o ro da zo'u ro de zo'u ga jo ctaipe lo me'oi .\AgdaRecord{Iso}.\ bei da bei de gi da me'oi .isomorphic.\ de

\begin{code}
record Iso {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    f₁ : A → B
    f₂ : B → A
    d₁ : (x : A) → x ≡ f₂ (f₁ x)
    d₂ : (x : B) → x ≡ f₁ (f₂ x)
\end{code}

\subsection{le se ctaipe pe lo du'u xu kau mapti la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.}
ni'o la .varik.\ cu jinvi le du'u ko'e se ctaipe pluja\sds  .i zo'e joi la'e di'u cu krinu le su'u la'o zoi.\ \D{\AgdaUnderscore{}⍨M}\ .zoi.\ me'oi .\AgdaKeyword{data}.\ co'e

.i la'o zoi.\ \IC{iso⍨}\ .zoi.\ jai filri'a tu'a zoi zoi.\ \texttt{5 = 1 *⍨ 5} .zoi.\ pe la'oi .APL.\\
.i la'o zoi.\ \IC{fancu⍨}\ .zoi.\ jai filri'a tu'a zoi zoi.\ \texttt{3125 = *⍨ 5} .zoi.\ pe la'oi .APL.\\

\begin{code}
data _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  iso⍨ : Iso A B → _⍨M A B
  fancu⍨ : (A → B) → _⍨M A B
\end{code}

\subsection{ko'a no'u la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ri ciksi ko'a fo lo te gerna be la .lojban.

\begin{code}
_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ iso⍨ M ⦄ = Iso.f₁ M
_⍨ ⦃ fancu⍨ M ⦄ = M
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}
ni'o lo me'oi .\AgdaKeyword{instance}.\ cu jai filri'a lo nu cmalu velcki pilno ko'a

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
    f₁ = Data.Product.swap;
    f₂ = Data.Product.swap;
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

  ⍨-f₁ : ∀ {a} → {A : Set a} → {B : Set a} → _⍨M (A → A → B) (A → B)
  ⍨-f₁ = fancu⍨ $ λ f x → f x x
\end{code}
\end{document}
