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
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\title{la'o zoi.\ \texttt{Truthbrary.Record.LLC} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{Truthbrary.Record.LL} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be la'o zoi.\ \F{LL} .zoi.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je noi tu'a ke'a filri'a lo nu pilno lo smimlu be la'oi .\F{List}.\ ku'o be'o je
	\item le velcki be le me'oi .\AgdaKeyword{instance}.\ pe la'o zoi.\ \F{LL} .zoi.\ be'o je
	\item le velcki be la'o zoi.\ \F{LC} .zoi.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je noi tu'a ke'a filri'a lo nu konkatena lo ctaipe be ko'a goi lo smimlu be lo liste lo ctaipe be ko'a ku'o be'o je
	\item le velcki be lo me'oi .\AgdaKeyword{instance}.\ pe la'o zoi.\ \F{LC} .zoi.
\end{itemize}

\section{le me'oi .preamble.}
\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.LLC where

open import Level
open import Data.Fin
  using (
    Fin
  )
  renaming (
    fromℕ to fromℕF;
    toℕ to toℕF
  )
open import Data.Nat
  hiding (
    _≟_;
    _≡ᵇ_
  )
open import Data.Vec
  renaming (
    [] to []ᵥ;
    _∷_ to _∷ᵥ_;
    replicate to replicateᵥ;
    length to lengthᵥ
  )
  hiding (
    reverse;
    _++_;
    map
  )
open import Function
open import Data.Bool
  hiding (
    _≟_;
    T
  )
open import Data.Char
  hiding (
    _≟_
  )
open import Data.List
  renaming (
    [] to []ₗ;
    _∷_ to _∷ₗ_;
    length to lengthₗ
  )
  hiding (
    reverse;
    _++_;
    map
  )
open import Data.Maybe
  hiding (
    map
  )
open import Data.String
  renaming (
    toList to toListₛ;
    fromList to fromListₛ
  )
  hiding (
    length;
    _≟_;
    _++_
  )
open import Truthbrary.Record.Eq
open import Relation.Nullary.Decidable
  using (
    isYes
  )
\end{code}
\section{la'oi .\F{LL}.}
ni'o ga jo zasti fa lo selvau be la'o zoi.\ \F{LL} \B x .zoi.\ gi la'oi .\B x.\ cu simsa la'oi .\F{List}.

.i ga jo la'oi .\B q.\ zasti je cu ctaipe la'o zoi.\ \F{LL} \B t .zoi.\ je cu ba'e drani gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \F{LL.e} \B q .zoi.\ se ctaipe lo selvau be lo ctaipe be la'oi .\B t.\ gi
	\item ga je la'o zoi.\ \F{LL.olen} \B q \B n .zoi.\ se ctaipe lo ro lazmi'u pe'a be la'oi .\B t.\ be'o poi la'oi .\B n.\ nilzilcmi ke'a gi
	\item ga je la'o zoi.\ \F{LL.[]} \B q .zoi.\ ctaipe la'o zoi.\ \F{LL.olen} \B q 0 .zoi\ldots je cu kunti gi
	\item ga je la'o zoi.\ \F{LL.l} \B q \B l .zoi.\ nilzilcmi la'o zoi.\ \B l .zoi. gi
	\item ga je pilno la'oi .\F{\_∷\_}.\ lo nu me'oi .prepend.\ gi
	\item la'o zoi.\ \F{LL.cev} \B q \Sym∘ \F{LL.vec} \B q .zoi.\ dunli la'oi .\F{id}.
\end{itemize}

\begin{code}
record LL {a} (A : Set a) : Set (Level.suc a)
  where
  field
    e : Set a
    olen : ℕ → Set a
    [] : olen 0
    l : A → ℕ
    _∷_ : e → (q : A) → olen $ ℕ.suc $ l q
    vec : (q : A) → Vec e $ l q
    cev : {n : ℕ} → Vec e n → olen n
\end{code}

\subsection{le fancu}

\subsubsection{la'oi .\F{\_∷\_}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka

\begin{code}
infixr 5 _∷_

_∷_ : ∀ {a} → {A : Set a}
     → ⦃ ALL : LL A ⦄
     → LL.e ALL → (q : A) → LL.olen ALL $ ℕ.suc $ LL.l ALL q
_∷_ ⦃ Q ⦄ = LL._∷_ Q
\end{code}

\subsubsection{la'oi .\F{[]}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka

\begin{code}
[] : ∀ {a} → {A : Set a}
   → ⦃ Q : LL A ⦄
   → LL.olen Q 0
[] ⦃ Q ⦄ = LL.[] Q
\end{code}

\subsubsection{la'oi .\F{length}.}
ni'o la'o zoi.\ \F{length} \B q .zoi.\ nilzilcmi la'o zoi.\ \B q .zoi.

\begin{code}
length : ∀ {a} → {A : Set a}
       → ⦃ LL A ⦄
       → A → ℕ
length ⦃ T ⦄ = LL.l T
\end{code}

\subsection{la'oi .\F{decaf}.}
ni'o ga jonai ga je la'o zoi.\ \B c .zoi.\ konkatena ja co'e la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B x .zoi.\ la'o zoi.\ \B b .zoi.\ gi ko'a goi la'o zoi.\ \F{decaf} \B c .zoi.\ me'oi .\F{just}.\ la'o zoi.\ \B x .zoi.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
decaf : ∀ {a} → {Bean : Set a}
      → ⦃ Q : LL Bean ⦄
      → ⦃ Eq $ LL.e Q ⦄
      → LL.e Q → LL.e Q → (j : Bean)
      → Maybe $ LL.olen Q $ LL.l Q j ∸ 2
decaf {_} {A} ⦃ Q ⦄ a b = Data.Maybe.map (LL.cev Q) ∘ f ∘ LL.vec Q
  where
  f : ∀ {n} → Vec (LL.e Q) n → Maybe $ Vec (LL.e Q) $ n ∸ 2
  f []ᵥ = nothing
  f (_ ∷ᵥ []ᵥ) = nothing
  f (x ∷ᵥ y ∷ᵥ z) = if conteven then just (delet q) else nothing
    where
    q = x ∷ᵥ y ∷ᵥ z
    r = Data.Vec.reverse
    delet = r ∘ t ∘ r ∘ t
      where
      t = Data.Vec.drop 1
    conteven = (px a q) ∧ (px b $ r q)
      where
      px = λ n → isYes ∘ _≟_ n ∘ Data.Vec.head
\end{code}

\section{la'oi .\F{map}.}
ni'o la .varik.\ cu sorpa'a lo nu le se ctaipe je zo'e cu banzuka  .i ku'i la'oi .\F{map}.\ cu smimlu la'oi .\texttt{map}.\ pe la'oi .Haskell.

\begin{code}
map : ∀ {a b} → {A : Set a} → {B : Set b}
    → ⦃ Q : LL A ⦄ → ⦃ R : LL B ⦄
    → (f : LL.e Q → LL.e R) → (x : A)
    → LL.olen R $ lengthᵥ $ Data.Vec.map f $ LL.vec Q x
map ⦃ Q ⦄ ⦃ R ⦄ f = LL.cev R ∘ Data.Vec.map f ∘ LL.vec Q
\end{code}

\section{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  liliList : ∀ {a} → {A : Set a} → LL $ List A
  liliList {_} {A} = record {
    e = A;
    olen = const $ List A;
    [] = []ₗ;
    l = lengthₗ;
    _∷_ = _∷ₗ_;
    vec = Data.Vec.fromList;
    cev = Data.Vec.toList}
  liliString : LL String
  liliString = record {
    e = Char;
    olen = const String;
    [] = "";
    l = Data.String.length;
    _∷_ = λ a → fromListₛ ∘ _∷ₗ_ a ∘ toListₛ;
    vec = Data.Vec.fromList ∘ Data.String.toList;
    cev = Data.String.fromList ∘ Data.Vec.toList}
  liliVec : ∀ {a} → {A : Set a} → {n : ℕ} → LL $ Vec A n
  liliVec {_} {A} {n'} = record {
    [] = []ᵥ;
    olen = Vec A;
    e = A;
    l = const n';
    _∷_ = _∷ᵥ_;
    vec = id;
    cev = id}
  liliℕ : LL ℕ
  liliℕ = record {
    [] = 0;
    olen = const ℕ;
    e = Fin 1;
    l = id;
    _∷_ = const ℕ.suc;
    vec = λ q → replicateᵥ {_} {_} {q} $ Data.Fin.fromℕ 0;
    cev = Data.Vec.length}
  liliFin : {n : ℕ} → LL $ Fin n
  liliFin = record {
    [] = fromℕF 0;
    olen = Fin ∘ _+_ 1;
    e = Fin 1;
    l = toℕF;
    _∷_ = const $ fromℕF ∘ ℕ.suc ∘ toℕF;
    vec = λ q → replicateᵥ {_} {_} {toℕF q} $ fromℕF 0;
    cev = fromℕF ∘ Data.Vec.length}
\end{code}

\section{la'oi .\F{LC}.}
ni'o ga jo ga je la'o zoi.\ \F{LC} \B A \B B .zoi.\ zasti gi la'o zoi.\ \B a .zoi.\ fa'u la'o zoi.\ \B b .zoi.\ ctaipe la'o zoi. B A .zoi.\ fa'u la'o zoi.\ \B B .zoi.\ gi la'o zoi.\ \B a \Sym{++} \B b .zoi.\ konkatena la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
record LC {a} (A B : Set a) ⦃ Q : LL A ⦄ ⦃ R : LL B ⦄ : Set a
  where
  field
    _++_ : (C : A) → (D : B) → LL.olen Q $ LL.l Q C + LL.l R D
\end{code}

\subsection{le fancu}

\subsubsection{la'oi .\F{\_++\_}.}
ni'o la'o zoi.\ \B a \Sym{++} \B b .zoi.\ konkatena la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.

\begin{code}
infixr 5 _++_

_++_ : ∀ {a} → {Bean CoolJ : Set a}
     → ⦃ T : LL Bean ⦄
     → ⦃ U : LL CoolJ ⦄
     → ⦃ C : LC Bean CoolJ ⦄
     → (BN : Bean) → (CJ : CoolJ)
     → LL.olen T $ LL.l T BN + LL.l U CJ
_++_ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ Q ⦄ = LC._++_ Q
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  LCList : ∀ {a} → {A : Set a}
         → LC (List A) (List A)
  LCList = record {_++_ = Data.List._++_}
  LCString : LC String String
  LCString = record {_++_ = Data.String._++_}
  LCVec : ∀ {a} → {A : Set a} → {m n : ℕ}
        → LC (Vec A m) (Vec A n)
  LCVec = record {_++_ = Data.Vec._++_}
  LCℕ : LC ℕ ℕ
  LCℕ = record {_++_ = Data.Nat._+_}
  LCFin : {m n : ℕ} → LC (Fin m) $ Fin n
  LCFin = record {_++_ = λ a → fromℕF ∘ _+_ (toℕF a) ∘ toℕF}
\end{code}
\end{document}
