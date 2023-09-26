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

\newcommand\cmene{Truthbrary.Record.Arithmetic}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o sa'u ko'a goi la'o zoi.\ \texttt\cmene\ .zoi.\ vasru zo'e poi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ kei je lo nu lo ctaipe be la'oi .\F{String}.\ cu binxo pe'a ru'e

.i sa'u nai ru'e vasru\ldots
\begin{itemize}
	\item vu'oi la'oi .\F{Show}.\ je la'oi .\F{show}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Show}.\ vu'o noi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ ku'o je
        \item vu'oi la'oi .\F{Read}.\ je la'oi .\F{readmaybe}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Read}.\ vu'o noi tu'a ke'a filri'a lo nu lo me'oi .\F{Maybe}.\ ctaipe cu selbi'o pe'a ru'e lo ctaipe be la'oi .\F{String}.
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
  using (
    suc;
    ℕ
  )
  renaming (
    _≟_ to _≟ₙ_
  )
open import Function
open import Data.Bool
  using (
    if_then_else_
  )
open import Data.Maybe
open import Data.Rational.Unnormalised as ℚᵘ
  using (
    1ℚᵘ;
    0ℚᵘ;
    mkℚᵘ;
    ℚᵘ
  )
open import Data.Integer
  using (
    0ℤ;
    1ℤ;
    ℤ
  )
import Data.Integer.DivMod
open import Data.Nat.DivMod
  using (
    _mod_
  )
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
\end{code}

\section{la'oi .\F{Arris}.}
ni'o ga jo ga je la'o zoi.\ \B a .zoi.\ drani mu'oi zoi.\ \F{Arris} \B A \B b .zoi.\ gi ko'a goi la'o zoi.\ \B x .zoi.\ ge'u fa'u ko'e goi la'o zoi.\ \B y .zoi.\ cu ctaipe la'o zoi.\ \B A .zoi.\ fa'u la'o zoi.\ \B B .zoi.\ gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{Arris.\_+\_} \B a \B x \B y .zoi.\ sumji ko'a ko'e gi
	\item ga je la'o zoi.\ \F{Arris.\_-\_} \B a \B x \B y .zoi.\ vujnu ko'a ko'e gi
	\item ga je la'o zoi.\ \F{Arris.\_*\_} \B a \B x \B y .zoi.\ pilji ko'a ko'e gi
	\item ga je la'o zoi.\ \F{Arris.\_/\_} \B a \B x \B y .zoi.\ dilcu ko'a ko'e gi
	\item ga je la'o zoi.\ \F{Arris.uyn₁} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.uyn₂} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.uyn*} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.uyn/} \B a \B x \B y .zoi.\ du li pa gi
	\item je la'o zoi.\ \F{Arris.zir₁} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.zir₂} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.zir+} \B a \B x \B y .zoi.\ je la'o zoi.\ \F{Arris.zir-} \B a \B x \B y .zoi.\ du li no gi
	\item co'e
\end{itemize}
.i la .varik.\ cu na jinvi le du'u sarcu fa lo nu .lojban.\ velcki la'o zoi.\ \F{1*1≡1} .zoi.\ je zo'e

\begin{code}
record Arris {a b c} (A : Set a) (B : Set b) : Set (lsuc $ a ⊔ b ⊔ c)
  where
  field
    _⊔+_ _⊔-_ _⊔*_ _⊔/_ : A → B → Set c
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
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = const $ const $ Maybe ℕ;
    _+_ = Data.Nat._+_;
    _-_ = Data.Nat._∸_;
    _*_ = Data.Nat._*_;
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
    r = const $ const ℕ
    deev : ℕ → ℕ → Maybe ℕ
    deev _ 0 = nothing
    deev a (suc b) = just $ Data.Nat.DivMod._/_ a $ suc b
    [matrix] = 3
  ariℤℤ = record {
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = const $ const $ Maybe ℤ;
    _+_ = Data.Integer._+_;
    _-_ = Data.Integer._-_;
    _*_ = Data.Integer._*_;
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
    r = const $ const ℤ
    deev : ℤ → ℤ → Maybe ℤ
    deev a b = csiz (λ x → Data.Integer.DivMod._div_ a b {x}) eek0
      where
      ∣b∣ = Data.Integer.∣ b ∣
      eek0 = ∣b∣ ≟ₙ 0
      csiz : (False $ ∣b∣ ≟ₙ 0 → ℤ) → Dec $ ∣b∣ ≡ 0 → Maybe ℤ
      csiz f (no q) = just $ f $ fromWitnessFalse q
      csiz _ (yes _) = nothing
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
    r = const $ const Float
  ariℚᵘℚᵘ : Arris ℚᵘ ℚᵘ
  ariℚᵘℚᵘ = record {
    _⊔+_ = r;
    _⊔-_ = r;
    _⊔*_ = r;
    _⊔/_ = const $ const $ Maybe ℚᵘ;
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
    r = const $ const ℚᵘ
    uyn = 1ℚᵘ
    zir = 0ℚᵘ
    deev : ℚᵘ → ℚᵘ → Maybe ℚᵘ
    deev m n with ∣↥n∣ ≟ₙ 0
      where
      ∣↥n∣ = Data.Integer.∣ ℚᵘ.↥ n ∣
    ... | no q = just $ (λ a → ℚᵘ._÷_ m n {a}) $ fromWitnessFalse q
    ... | yes _ = nothing
\end{code}

\section{la'oi .\F{\_+\_}.}
ni'o la'o zoi.\ B a \Sym + \B b .zoi.\ sumji la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_+_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A) → (y : B) → Arris._⊔+_ Q x y
_+_ ⦃ Q ⦄ = Arris._+_ Q
\end{code}

\section{la'oi .\F{\_-\_}.}
ni'o la'o zoi.\ B a \Sym - \B b .zoi.\ vujnu la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_-_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A) → (y : B) → Arris._⊔-_ Q x y
_-_ ⦃ Q ⦄ = Arris._-_ Q
\end{code}

\section{la'oi .\F{\_*\_}.}
ni'o la'o zoi.\ B a \Sym * \B b .zoi.\ pilji la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_*_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A) → (y : B) → Arris._⊔*_ Q x y
_*_ ⦃ Q ⦄ = Arris._*_ Q
\end{code}

\section{la'oi .\F{\_/\_}.}
ni'o la'o zoi.\ B a \Sym / \B b .zoi.\ dilcu la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
_/_ : ∀ {a b c} → {A : Set a} → {B : Set b}
    → ⦃ Q : Arris {a} {b} {c} A B ⦄
    → (x : A) → (y : B) → Arris._⊔/_ Q x y
_/_ ⦃ Q ⦄ = Arris._/_ Q
\end{code}
\end{document}
