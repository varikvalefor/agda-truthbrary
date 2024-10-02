\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{MnSymbol}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathbb{Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{↥}{\ensuremath{\mathnormal{\upmapsto}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\mathrm{s}}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_\mathrm{n}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\mathrm{u}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\mathrm{v}}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\mathrm{b}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathrm{m}}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⊔}{\ensuremath{\mathnormal{\sqcup}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{\mid}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\AgdaFunction{#1}}}

\newcommand\cmene{Truthbrary.Record.Arithmetic}

\title{la'o zoi.\ \texttt{\cmene}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o sa'u ko'a goi la'o zoi.\ \texttt\cmene\ .zoi.\ vasru lo jai be filri'a tu'a lo namcu

.i sa'u nai ru'e ko'a vasru\ldots
\begin{itemize}
	\item le velcki be ko'e goi la'oi .\AgdaRecord{Arris}.\ noi tu'a ke'a filri'a lo nu ciksi ja co'e ko'a goi lo'i namcu ge'u je lo fancu be ko'a ku'o be'o je
	\item le velcki be le me'oi .\AgdaKeyword{instance}.\ be ko'e be'o be'o je
	\item le velcki be vu'oi la'o zoi.\ \F{\AgdaUnderscore+\AgdaUnderscore}\ .zoi.\ je zo'e vu'o noi tu'a ke'a filri'a tu'a lo sumji je zo'e
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.Arithmetic where

open import Data.Float
  using (
    Float
  )
open import Level
  using (
    Level;
    _⊔_
  )
  renaming (
    suc to lsuc
  )
open import Data.Nat
  as ℕ
  using (
    suc;
    ℕ
  )
open import Function
  using (
    _∘_;
    _$_
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    just
  )
open import Data.Integer
  as ℤ
  using (
    0ℤ;
    1ℤ;
    ℤ
  )
open import Data.Nat.DivMod
  as ℕ
  using (
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Data.Rational.Unnormalised
  as ℚᵘ
  using (
    mkℚᵘ;
    1ℚᵘ;
    0ℚᵘ;
    ℚᵘ
  )
open import Relation.Nullary.Decidable
  using (
    fromWitnessFalse;
    False
  )
open import Relation.Binary.Definitions
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    _≡_
  )

import Data.Integer.DivMod
\end{code}

\section{la'oi .\AgdaRecord{Arris}.}
ni'o ga jo ga je la'o zoi.\ \B a .zoi.\ drani mu'oi zoi.\ \AgdaRecord{Arris} \B A \B B .zoi.\ gi ko'a goi la'o zoi.\ \B x .zoi.\ ge'u fa'u ko'e goi la'o zoi.\ \B y .zoi.\ cu ctaipe la'o zoi.\ \B A .zoi.\ fa'u la'o zoi.\ \B B .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{Arris.\AgdaUnderscore+\AgdaUnderscore} \B a \B x \B y .zoi.\ sumji ko'a ko'e gi
	\item ga je la'o zoi.\ \AgdaField{Arris.\AgdaUnderscore-\AgdaUnderscore} \B a \B x \B y .zoi.\ vujnu ko'a ko'e gi
	\item ga je la'o zoi.\ \AgdaField{Arris.\AgdaUnderscore*\AgdaUnderscore} \B a \B x \B y .zoi.\ pilji ko'a ko'e gi
	\item ga je la'o zoi.\ \AgdaField{Arris.\AgdaUnderscore/\AgdaUnderscore} \B a \B x \B y .zoi.\ dilcu ko'a ko'e gi
	\item ga je la'o zoi.\ \AgdaField{Arris.uyn₁} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.uyn₂} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.uyn*} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.uyn/} \B a \B x \B y .zoi.\ du li pa gi
	\item ga je la'o zoi.\ \AgdaField{Arris.zir₁} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.zir₂} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.zir+} \B a \B x \B y .zoi.\ je la'o zoi.\ \AgdaField{Arris.zir-} \B a \B x \B y .zoi.\ du li no gi
	\item co'e
\end{itemize}

.i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo fe zo'e je la'o zoi.\ \AgdaField{Arris.1*1≡1} .zoi.

\begin{code}
record Arris {a b c} (A : Set a) (B : Set b) : Set (lsuc $ a ⊔ b ⊔ c)
  where
  field
    _⊔+_
     _⊔-_
     _⊔*_
     _⊔/_ : A → B → Set c
  FC : (A → B → Set c) → Set (a ⊔ b ⊔ c)
  FC f = (x : A) → (y : B) → f x y
  field
    _+_ : FC _⊔+_
    _-_ : FC _⊔-_
    _*_ : FC _⊔*_
    _/_ : FC _⊔/_
    uyn₁ : A
    uyn₂ : B
    uyn* : uyn₁ ⊔* uyn₂
    uyn/ : uyn₁ ⊔/ uyn₂
    zir₁ : A
    zir₂ : B
    zir+ : zir₁ ⊔+ zir₂
    zir- : zir₁ ⊔- zir₂
    1*1≡1 : uyn₁ * uyn₂ ≡ uyn*
    1/1≡1 : uyn₁ / uyn₂ ≡ uyn/
    0+0≡0 : zir₁ + zir₂ ≡ zir+
    0-0≡0 : zir₁ - zir₂ ≡ zir-
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  ariℕℕ = record {
    _⊔+_ = Cℕ;
    _⊔-_ = Cℕ;
    _⊔*_ = Cℕ;
    _⊔/_ = λ _ _ → Maybe ℕ;
    _+_ = ℕ._+_;
    _-_ = ℕ._∸_;
    _*_ = ℕ._*_;
    _/_ = deev;
    uyn₁ = 1;
    uyn₂ = 1;
    uyn* = 1;
    uyn/ = just 1;
    zir₁ = 0;
    zir₂ = 0;
    zir+ = 0;
    zir- = 0;
    1*1≡1 = refl;
    1/1≡1 = refl;
    0+0≡0 = refl;
    0-0≡0 = refl}
    where
    Cℕ = λ _ _ → ℕ
    deev : ℕ → ℕ → Maybe ℕ
    deev _ 0 = nothing
    deev a (suc b) = just $ a ℕ./ suc b

  ariℤℤ = record {
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = _;
    _+_ = ℤ._+_;
    _-_ = ℤ._-_;
    _*_ = ℤ._*_;
    _/_ = deev;
    uyn₁ = 1ℤ;
    uyn₂ = 1ℤ;
    uyn* = 1ℤ;
    uyn/ = just 1ℤ;
    zir₁ = 0ℤ;
    zir₂ = 0ℤ;
    zir+ = 0ℤ;
    zir- = 0ℤ;
    1*1≡1 = refl;
    1/1≡1 = refl;
    0+0≡0 = refl;
    0-0≡0 = refl}
    where
    r = λ _ _ → ℤ
    deev : ℤ → ℤ → Maybe ℤ
    deev a b = cysiz (λ x → Data.Integer.DivMod._div_ a b {x}) eek0
      where
      ∣b∣ = ℤ.∣ b ∣
      eek0 = ∣b∣ ℕ.≟ 0
      cysiz : (False $ ∣b∣ ℕ.≟ 0 → ℤ) → Dec $ ∣b∣ ≡ 0 → Maybe ℤ
      cysiz f (no j) = just $ f $ fromWitnessFalse j
      cysiz _ (yes _) = nothing

  ariFloatFloat : Arris Float Float
  ariFloatFloat = record {
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = r;
    _+_ = Data.Float._+_;
    _-_ = Data.Float._-_;
    _*_ = Data.Float._*_;
    _/_ = Data.Float._÷_;
    uyn₁ = uyn;
    uyn₂ = uyn;
    uyn* = uyn;
    uyn/ = uyn;
    zir₁ = zir;
    zir₂ = zir;
    zir+ = zir;
    zir- = zir;
    1*1≡1 = refl;
    1/1≡1 = refl;
    0+0≡0 = refl;
    0-0≡0 = refl}
    where
    uyn = Data.Float.fromℕ 1
    zir = Data.Float.fromℕ 0
    r = λ _ _ → Float

  ariℚᵘℚᵘ : Arris ℚᵘ ℚᵘ
  ariℚᵘℚᵘ = record {
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = λ _ _ → Maybe ℚᵘ;
    _+_ = ℚᵘ._+_;
    _-_ = ℚᵘ._-_;
    _*_ = ℚᵘ._*_;
    _/_ = deev;
    uyn₁ = uyn;
    uyn₂ = uyn;
    uyn* = uyn;
    uyn/ = just uyn;
    zir₁ = zir;
    zir₂ = zir;
    zir+ = zir;
    zir- = zir;
    1*1≡1 = refl;
    1/1≡1 = refl;
    0+0≡0 = refl;
    0-0≡0 = refl}
    where
    r = λ _ _ → ℚᵘ
    uyn = 1ℚᵘ
    zir = 0ℚᵘ
    deev : _ → _ → Maybe ℚᵘ
    deev m n = spit {P? = ∣↥n∣ ℕ.≟_} (λ N → ℚᵘ._÷_ m n {N}) $ _ ℕ.≟ 0
      where
      ∣↥n∣ = ℤ.∣ ℚᵘ.↥ n ∣
      spit : ∀ {a b p}
           → {A : Set a}
           → {B : Set b}
           → {P : B → Set p}
           → {P? : (x : B) → Dec $ P x}
           → {x : B}
           → (False $ P? x → A)
           → Dec $ P x
           → Maybe A
      spit f (no q) = just $ f $ fromWitnessFalse q
      spit _ _ = nothing
\end{code}

\section{la'oi .\F{\AgdaUnderscore+\AgdaUnderscore}.}
ni'o la'o zoi.\ B a \OpF + \B b .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_+_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A)
    → (y : B)
    → Arris._⊔+_ Q x y
_+_ ⦃ Q ⦄ = Arris._+_ Q
\end{code}

\section{la'oi .\F{\AgdaUnderscore-\AgdaUnderscore}.}
ni'o la'o zoi.\ B a \OpF - \B b .zoi.\ vujnu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_-_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A) → (y : B) → Arris._⊔-_ Q x y
_-_ ⦃ Q ⦄ = Arris._-_ Q
\end{code}

\section{la'oi .\F{\AgdaUnderscore*\AgdaUnderscore}.}
ni'o la'o zoi.\ B a \OpF * \B b .zoi.\ pilji la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_*_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {c = c} A B ⦄
    → (x : A)
    → (z : B)
    → Arris._⊔*_ Q x z
_*_ ⦃ Q ⦄ = Arris._*_ Q
\end{code}

\section{la'oi .\F{\AgdaUnderscore/\AgdaUnderscore}.}
ni'o la'o zoi.\ B a \OpF / \B b .zoi.\ dilcu la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_/_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {c = c} A B ⦄
    → (x : A)
    → (z : B)
    → Arris._⊔/_ Q x z
_/_ ⦃ Q ⦄ = Arris._/_ Q
\end{code}
\end{document}
