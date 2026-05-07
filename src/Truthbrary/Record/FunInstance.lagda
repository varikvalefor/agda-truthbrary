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
\newunicodechar{≡}{\ensuremath{\mathnormal\cong}}
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

\section{la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.\ je lo jai filri'a be tu'a ri}

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

\begin{code}
data _⍨M {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  iso⍨ : Iso A B → _⍨M A B
  fancu⍨ : (A → B) → _⍨M A B
\end{code}

\subsection{la'o zoi.\ \AgdaFunction{\AgdaUnderscore{}⍨}\ .zoi.}

\begin{code}
_⍨ : ∀ {a b} → {A : Set a} → {B : Set b} → ⦃ _⍨M A B ⦄ → A → B
_⍨ ⦃ iso⍨ M ⦄ = Iso.f₁ M
_⍨ ⦃ fancu⍨ M ⦄ = M
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  ⍨-⍨ : ∀ {a b} → {A : Set a} → {B : Set b}
     → ⦃ Iso A B ⦄
     → _⍨M B A
  ⍨-⍨ ⦃ M ⦄ = iso⍨ $ record {
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
