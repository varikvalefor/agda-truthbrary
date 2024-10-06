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

\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb{Q}}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\mathrm{b}}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^l}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^r}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{′}{\ensuremath{\mathnormal{\prime}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\Colon}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\AgdaFunction{#1}}}

\title{la'o zoi.\ \texttt{Truthbrary.Record.Eq} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{Truthbrary.Record.Eq} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be ko'a goi la'oi .\F{\AgdaUnderscore≟\AgdaUnderscore}.\ noi tu'a ke'a filri'a lo nu jdice lo jei dunli be'o je
	\item le velcki be ko'e goi le me'oi .\AgdaKeyword{record}.\ poi ke'a jicmu ko'a be'o je
	\item le me'oi .\AgdaKeyword{instance}.\ pe ko'e
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.Eq where


import Level
import Data.Fin
import Data.Char
import Data.Float
import Data.String
import Data.Maybe.Properties
import Data.These.Properties
import Data.Product.Properties

open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
open import Function
open import Data.Bool
  using (
    Bool
  )
open import Data.Maybe
open import Data.These
  using (
    These
  )
open import Data.Integer
  using (
    ℤ
  )
open import Data.Product
open import Data.Rational
  using (
    ℚ
  )
open import Data.List
  using (
    List;
    _∷_
  )
open import Data.Vec
  using (
    Vec
  )
  renaming (
    _∷_ to _∷ᵥ_;
    [] to []ᵥ
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no;
    ¬_
  )
open import Relation.Nullary.Decidable
open import Relation.Binary.Structures
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

import Data.Vec.Properties as DVP
\end{code}

\section{la'oi .\AgdaRecord{Eq}.}
\newcommand\eqq[1]{ga jonai ga je la'o zoi.\ \B a .zoi.\ du la'o zoi.\ \B b .zoi.\ gi la'oi .\F{true}.\ du ko'a goi la'o zoi.\ \F{isYes} \OpF \$ #1\ .zoi.\ gi ko'a du la'o zoi.\ \F{false} .zoi.}
ni'o ga jo ga je la'o zoi.\ \B Q .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Eq} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ je la'o zoi.\ \B b .zoi.\ ctaipe la'o zoi.\ \B A .zoi.\ gi \eqq{\F{Eq.\AgdaUnderscore≟\AgdaUnderscore} \B Q \B a \B b}

\begin{code}
record Eq {a} (A : Set a) : Set (Level.suc a)
  where
  field
    _≟_ : DecidableEquality A
\end{code}

\subsection{la'oi .\F{\AgdaUnderscore≟\AgdaUnderscore}.}
ni'o \eqq{\B a \OpF ≟ \B b}

\begin{code}
_≟_ : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → DecidableEquality A
_≟_ ⦃ Q ⦄ = Eq._≟_ Q
\end{code}

\subsection{la'oi .\F{\AgdaUnderscore≡ᵇ\AgdaUnderscore}.}

\begin{code}
_≡ᵇ_ : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → A → A → Bool
_≡ᵇ_ = isYes ∘₂ _≟_
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  Eqℕ : Eq ℕ
  Eqℕ = record {_≟_ = ℕ._≟_}
  Eqℚ : Eq ℚ
  Eqℚ = record {_≟_ = Data.Rational._≟_}
  Eqℤ : Eq ℤ
  Eqℤ = record {_≟_ = Data.Integer._≟_}
  EqBool : Eq Bool
  EqBool = record {_≟_ = Data.Bool._≟_}
  -- | All I've got with me is a pistol and an...
  EqProd : ∀ {a b} → {A : Set a} → {B : Set b}
         → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
         → Eq $ A × B
  EqProd = record {_≟_ = Data.Product.Properties.≡-dec _≟_ _≟_}
  EqString : Eq Data.String.String
  EqString = record {_≟_ = Data.String._≟_}
  EqChar : Eq Data.Char.Char
  EqChar = record {_≟_ = Data.Char._≟_}
  EqFloat : Eq Data.Float.Float
  EqFloat = record {_≟_ = Data.Float._≟_}
  EqFin : {n : ℕ} → Eq $ Data.Fin.Fin n
  EqFin = record {_≟_ = Data.Fin._≟_}
  EqMaybe : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Eq $ Maybe A
  EqMaybe = record {_≟_ = Data.Maybe.Properties.≡-dec _≟_}
  EqThese : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
          → Eq $ These A B
  EqThese = record {_≟_ = Data.These.Properties.≡-dec _≟_ _≟_}
  EqList : ∀ {a} → {A : Set a} → ⦃ Eq A ⦄ → Eq $ List A
  EqList {A = A} ⦃ Q ⦄ = record {_≟_ = f}
    where
    -- | Tick-tock, tick-tock, tick-tock!
    doomsday : ∀ {a} → {A : Set a}
             → {x y : A} → {xs ys : List A}
             → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
    doomsday refl refl = refl
    notBigInto : ∀ {a} → {A : Set a}
               → {x y : A} → {xs ys : List A}
               → x ∷ xs ≡ y ∷ ys → xs ≡ ys
    notBigInto refl = refl
    leadneck : ∀ {a} → {A : Set a}
             → {x y : A} → {xs ys : List A}
             → ¬ (x ≡ y) → ¬ (x ∷ xs ≡ y ∷ ys)
    leadneck = _∘ hillbilly
      where
      hillbilly : ∀ {a} → {A : Set a}
                → {x y : A}
                → {xs ys : List A}
                → x ∷ xs ≡ y ∷ ys
                → x ≡ y
      hillbilly refl = refl
    bork : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → ⦃ Eq A ⦄
         → (t v : A)
         → (x z : B)
         → Dec $ x ≡ z
         → (t ≡ v → x ≡ z → C)
         → (t ≡ v → ¬ (x ≡ z) → C)
         → (¬ (t ≡ v) → x ≡ z → C)
         → (¬ (t ≡ v) → ¬ (x ≡ z) → C)
         → C
    bork {C = C} t v x z d f g j k = spit (t ≟ v) d
      where
      spit : Dec $ t ≡ v → Dec $ x ≡ z → C
      spit (yes a) (yes b) = f a b
      spit (yes a) (no b) = g a b
      spit (no a) (yes b) = j a b
      spit (no a) (no b) = k a b
    f : DecidableEquality $ List A
    f List.[] List.[] = yes refl
    f (_ ∷ _) List.[] = no $ λ ()
    f List.[] (_ ∷ _) = no $ λ ()
    f (x ∷ xs) (y ∷ ys) = bork x y xs ys (f xs ys) booty messiah arm ltd
      where
      -- .i cumki fa lo nu vimcu le ctaipe velcki
      -- .i ku'i la .varik. cu jinvi le du'u lo nu
      -- jmina ja co'e le ctaipe velcki cu filri'a
      -- lo nu jimpe... kei kei je cu djica lo nu
      -- frili fa lo nu jimpe
      booty : x ≡ y → xs ≡ ys → Dec $ x ∷ xs ≡ y ∷ ys
      booty jorts _ = map′ (doomsday jorts) notBigInto $ f xs ys
      arm : ¬ (x ≡ y) → xs ≡ ys → Dec $ x ∷ xs ≡ y ∷ ys
      arm wrestling _ = no $ leadneck wrestling
      -- | .i la .varik. cu jinvi le du'u na xlabebna
      -- fa le versiio be le cmene be'o poi co'e ke'a
      -- pu lo nu gubygau le ctaipe... kei kei jenai
      -- le du'u le versiio poi ke'a jai cabna cu
      -- mutce le ka ce'u na xlabebna... kei kei je
      -- ku'i cu nelci le jalge be le nu zo'oi
      -- .messiah. cmene le ctaipe
      messiah : x ≡ y → ¬ (xs ≡ ys) → Dec $ x ∷ xs ≡ y ∷ ys
      messiah eek = map′ (doomsday eek) notBigInto ∘ no
      ltd : ¬ (x ≡ y) → ¬ (xs ≡ ys) → Dec $ x ∷ xs ≡ y ∷ ys
      ltd quality _ = no $ leadneck quality
  EqVec : ∀ {a} → {A : Set a} → {n : ℕ} → ⦃ Eq A ⦄
        → Eq $ Vec A n
  EqVec {_} {A} {n} = record {_≟_ = f}
    where
    -- ni'o srana la'oi .EqVec. fa
    -- lo so'i pinka pe la'oi .EqList.
    doomsday : ∀ {a} → {A : Set a} → {m : ℕ}
             → {x y : A} → {xs ys : Vec A m}
             → x ≡ y → xs ≡ ys → x ∷ᵥ xs ≡ y ∷ᵥ ys
    doomsday refl refl = refl
    bork : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
         → ⦃ Eq A ⦄
         → (t v : A)
         → (x z : B)
         → Dec $ x ≡ z
         → (t ≡ v → x ≡ z → C)
         → (t ≡ v → ¬ (x ≡ z) → C)
         → (¬ (t ≡ v) → x ≡ z → C)
         → (¬ (t ≡ v) → ¬ (x ≡ z) → C)
         → C
    bork {C = C} t v x z d f g j k = spit (t ≟ v) d
      where
      spit : Dec $ t ≡ v → Dec $ x ≡ z → C
      spit (yes a) (yes b) = f a b
      spit (yes a) (no b) = g a b
      spit (no a) (yes b) = j a b
      spit (no a) (no b) = k a b
    f : {n : ℕ} → DecidableEquality $ Vec A n
    f []ᵥ []ᵥ = yes refl
    f (x ∷ᵥ xs) (y ∷ᵥ ys) = bork x y xs ys (f xs ys) booty messiah arm ltd
      where
      booty : x ≡ y → xs ≡ ys → Dec $ x ∷ᵥ xs ≡ y ∷ᵥ ys
      booty jorts _ = map′ (doomsday jorts) DVP.∷-injectiveʳ $ f xs ys
      arm : ∀ {a} → {A : Set a} → {n : ℕ}
          → {x y : A} → {xs ys : Vec A n}
          → ¬ (x ≡ y) → xs ≡ ys → Dec $ x ∷ᵥ xs ≡ y ∷ᵥ ys
      arm wrestling _ = no $ wrestling ∘ DVP.∷-injectiveˡ
      messiah : x ≡ y → ¬ (xs ≡ ys) → Dec $ x ∷ᵥ xs ≡ y ∷ᵥ ys
      messiah eek = map′ (doomsday eek) DVP.∷-injectiveʳ ∘ no
      ltd : ¬ (x ≡ y) → ¬ (xs ≡ ys) → Dec $ x ∷ᵥ xs ≡ y ∷ᵥ ys
      ltd quality _ = no $ quality ∘ DVP.∷-injectiveˡ
  EqSum : ∀ {a b} → {A : Set a} → {B : Set b}
        → ⦃ Eq A ⦄ → ⦃ Eq B ⦄
        → Eq $ A ⊎ B
  EqSum = record {_≟_ = Q}
    where
    inj₁-inj : ∀ {a b} → {A : Set a} → {B : Set b}
             → {x y : A}
             → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y
             → x ≡ y
    inj₁-inj refl = refl
    inj₂-inj : ∀ {a b} → {A : Set a} → {B : Set b} → {x y : B}
             → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
    inj₂-inj refl = refl
    Q : DecidableEquality $ _ ⊎ _
    Q (inj₁ t) (inj₁ l) = map′ (cong inj₁) inj₁-inj $ t ≟ l
    Q (inj₂ t) (inj₂ l) = map′ (cong inj₂) inj₂-inj $ t ≟ l
    Q (inj₁ _) (inj₂ _) = no $ λ ()
    Q (inj₂ _) (inj₁ _) = no $ λ ()
\end{code}
\end{document}
