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
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{∃}{\ensuremath{\mathnormal{\exists}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{ⁿ}{\ensuremath{\mathnormal{^n}}}
\newunicodechar{ʸ}{\ensuremath{\mathnormal{^y}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal{\in}}}
\newunicodechar{∉}{\ensuremath{\mathnormal{\notin}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{la'o zoi.\ \texttt{Truthbrary.Record.LLC} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{Truthbrary.Record.LL} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be la'o zoi.\ \AgdaRecord{LL} .zoi.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je cu jai filri'a lo nu pilno lo smimlu be la'oi .\D{Vec}.\ ku'o be'o je
        \item le velcki be la'o zoi.\ \F{dist} .zoi.\ noi ke'a jai filri'a lo nu kanji lo mu'oi glibau.\ HAMMING weight .glibau.\ ku'o be'o je
	\item le velcki be la'o zoi.\ \F{\AgdaUnderscore{}∈\AgdaUnderscore} .zoi.\ noi tu'a ke'a filri'a lo nu ciksi lo ctaipe be lo su'u vasru ku'o be'o je le velcki be la'o zoi.\ \F{\AgdaUnderscore∉\AgdaUnderscore} .zoi.\ noi tu'a ke'a filri'a lo nu ciksi lo ctaipe be lo su'u na vasru ku'o be'o je
	\item le velcki be la'o zoi.\ \F{\AgdaUnderscore∈₂\AgdaUnderscore} .zoi.\ noi ke'a smimlu la'o zoi.\ \F{\AgdaUnderscore{}∈\AgdaUnderscore}\ .zoi.\ be'o je le velcki be la'o zoi.\ \F{\AgdaUnderscore{}∉₂\AgdaUnderscore}\ .zoi.\ noi ke'a smimlu la'o zoi.\ \F{\AgdaUnderscore{}∉\AgdaUnderscore}\ .zoi.\ be'o je
	\item le velcki be la'o zoi.\ \F{\AgdaUnderscore{}∈₂?\AgdaUnderscore} .zoi.\ noi ke'a me'oi .\AgdaRecord{Dec}.\ ke mu'oi zoi.\ \F{\AgdaUnderscore{}∈₂\AgdaUnderscore}\ .zoi.\ co'e be'o je le velcki be la'o zoi.\ \F{\AgdaUnderscore{}∉₂?\AgdaUnderscore}\ .zoi.\ noi ke'a me'oi .\AgdaRecord{Dec}.\ ke mu'oi zoi.\ \F{\AgdaUnderscore{}∉₂\AgdaUnderscore}\ .zoi.\ co'e be'o je
	\item le velcki be le me'oi .\AgdaKeyword{instance}.\ pe la'o zoi.\ \AgdaRecord{LL} .zoi.\ be'o je
	\item le velcki be la'o zoi.\ \AgdaRecord{LC} .zoi.\ noi ke'a me'oi .\AgdaKeyword{record}.\ je noi tu'a ke'a filri'a lo nu konkatena lo ctaipe be ko'a goi lo smimlu be lo liste lo ctaipe be ko'a ku'o be'o je
	\item le velcki be le me'oi .\AgdaKeyword{instance}.\ pe la'o zoi.\ \AgdaRecord{LC} .zoi.
\end{itemize}

\section{le me'oi .preamble.}
\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.LLC where

open import Level
  using (
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
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
    filter to filterₗ;
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
open import Data.Product
  using (
    uncurry;
    _,_
  )
open import Data.String
  renaming (
    fromList to fromListₛ;
    toList to toListₛ
  )
  hiding (
    length;
    _≟_;
    _++_
  )
open import Data.Product
  using (
    ∃;
    Σ
  )
open import Relation.Unary
  using (
    Pred
  )
open import Relation.Nullary
open import Truthbrary.Record.Eq
open import Relation.Nullary.Decidable
  using (
    isYes
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≢_;
    _≡_
  )

import Data.Vec.Relation.Unary.Any
  as DVRUA
  using (
    any?;
    Any
  )
import Data.Vec.Relation.Unary.All
  as DVRUL
  using (
    all?;
    All
  )
\end{code}

\section{la'oi .\AgdaRecord{LL}.}
ni'o ga jo ctaipe la'o zoi.\ \AgdaRecord{LL} \B x .zoi.\ gi la'oi .\B x.\ simsa la'oi .\D{Vec}.  .i zo'oi .LL.\ cmene ki'u le su'u zo'oi .LL.\ cmene le pa moi noi pilno ke'a lo nu ciksi lo su'u simsa la'oi .\D{List}.

.i ga jo la'oi .\B q.\ ctaipe la'o zoi.\ \AgdaRecord{LL} \B t .zoi.\ je cu ba'e drani gi\ldots
\begin{itemize}
	\item ga je la'o zoi.\ \AgdaField{LL.e} \B q .zoi.\ se ctaipe lo selvau be lo ctaipe be la'oi .\B t.\ gi
	\item ga je la'o zoi.\ \AgdaField{LL.olen} \B q \B n .zoi.\ se ctaipe lo ro ctaipe be la'oi .\B t.\ be'o poi la'oi .\B n.\ nilzilcmi ke'a gi
	\item ga je la'o zoi.\ \AgdaField{LL.[]} \B q .zoi.\ ctaipe la'o zoi.\ \AgdaField{LL.olen} \B q 0 .zoi\ldots je cu kunti gi
	\item ga je la'o zoi.\ \AgdaField{LL.l} \B q \B l .zoi.\ nilzilcmi la'oi .\B l.\ gi
	\item ga je pilno la'oi .\AgdaField{LL.\AgdaUnderscore∷\AgdaUnderscore}.\ lo nu me'oi .prepend.\ gi
	\item ga je ro da poi ke'a kacna'u je cu mleca zo'u lo meirmoi be la'oi .\B x.\ bei fo da cu meirmoi la'o zoi.\ \AgdaField{LL.vec} \B q \B x .zoi.\ fo da gi
        \item ro da poi ke'a kacna'u je cu mleca zo'u lo meirmoi be la'oi .\B z.\ bei fo da cu meirmoi la'o zoi.\ \AgdaField{LL.cev} \B q \B z .zoi.\ fo da
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

\subsubsection{la'oi .\F{\AgdaUnderscore∷\AgdaUnderscore}.}
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
ni'o la'o zoi.\ \F{length} \B q .zoi.\ nilzilcmi la'oi .\B q.

\begin{code}
length : ∀ {a} → {A : Set a}
       → ⦃ LL A ⦄
       → A → ℕ
length ⦃ T ⦄ = LL.l T
\end{code}

\subsubsection{la'oi .\F{vec}.}
ni'o la'o zoi.\ \F{vec} \B a .zoi.\ me'oi .equivalent.\ la'oi .\B a.

\begin{code}
vec : ∀ {a} → {Bean : Set a}
    → ⦃ Q : LL Bean ⦄
    → (lima : Bean) → Vec (LL.e Q) $ LL.l Q lima
vec ⦃ Q ⦄ = LL.vec Q
\end{code}

\subsubsection{la'oi .\F{cev}.}
ni'o la'o zoi.\ \F{cev} \B a .zoi.\ me'oi .equivalent.\ la'oi .\B a.

\begin{code}
cev : ∀ {a} → {Bean : Set a}
    → ⦃ Q : LL Bean ⦄
    → {n : ℕ} → Vec (LL.e Q) n → LL.olen Q n
cev ⦃ Q ⦄ = LL.cev Q
\end{code}

\subsection{la'oi .\F{decaf}.}
ni'o ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \F{decaf} \B a \B b \B c .zoi.\ gi ga je la'oi .\B c.\ konkatena ja co'e la'oi .\B a.\ la'oi .\B x.\ la'oi .\B b.\ gi ko'a me'oi .\AgdaInductiveConstructor{just}.\ la'oi .\B x.

\begin{code}
decaf : ∀ {a} → {Bean : Set a}
      → ⦃ Q : LL Bean ⦄
      → ⦃ Eq $ LL.e Q ⦄
      → LL.e Q → LL.e Q → (j : Bean)
      → Maybe $ LL.olen Q $ LL.l Q j ∸ 2
decaf ⦃ Q ⦄ a b = Data.Maybe.map cev ∘ f ∘ vec
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
    conteven = (pamoi a q) ∧ (pamoi b $ r q)
      where
      pamoi = λ n → isYes ∘ _≟_ n ∘ Data.Vec.head
\end{code}

\subsection{la .\F{map}.}
ni'o la .varik.\ cu pacna lo nu banzuka fa zo'e je le se ctaipe  .i ku'i la .\F{map}.\ cu smimlu la .\texttt{map}.\ pe la'oi .Haskell.

\begin{code}
map : ∀ {a b} → {A : Set a} → {B : Set b}
    → ⦃ Q : LL A ⦄ → ⦃ R : LL B ⦄
    → (f : LL.e Q → LL.e R) → (x : A)
    → LL.olen R $ length x
map f = cev ∘ Data.Vec.map f ∘ vec
\end{code}

\subsection{la .\F{garden}.}
ni'o ga jonai la'o zoi.\ \B q\ .zoi.\ du ko'a goi la'o zoi.\ \F{garden} \B f \B q \B x .zoi.\ gi ga je la'o zoi.\ \AgdaInductiveConstructor{just} \B Q .zoi.\ cmima la'o zoi.\ \F{map} \B f \B x .zoi.\ je cu pamoi lo'i ro me'oi .\AgdaInductiveConstructor{just}.\ poi ke'a cmima ko'a gi ko'a du la'oi .\B Q.

\begin{code}
garden : ∀ {a b} → {CoolJ : Set a} → {B : Set b}
       → ⦃ Q : LL CoolJ ⦄
       → (LL.e Q → Maybe B) → B → CoolJ → B
garden the west gate = g2 the west $ vec gate
  where
  g2 : ∀ {a b} → {A : Set a} → {B : Set b} → {n : ℕ}
     → (A → Maybe B) → B → Vec A n → B
  g2 f d (x ∷ᵥ xs) = maybe id (g2 f d xs) $ f x
  g2 _ d []ᵥ = d
\end{code}

\subsection{la'oi .\F{dist}.}
ni'o ko'a goi la'o zoi.\ \F{dist} \B a \B b .zoi.\ mu'oi glibau.\ HAMMING distance .glibau.\ la'oi .\B a.\ la'oi .\B b.

.i smudu'i fa lu ko'a nilzilcmi lo'i ro co'e poi ga jo ke'a du la'oi .\B n.\ gi la'o zoi.\ \F{lookup} \B a \B n .zoi.\ na dunli la'o zoi.\ \F{lookup} \B b \B n .zoi.\ li'u

\begin{code}
dist : ∀ {a} → {A : Set a}
     → ⦃ Bean : LL A ⦄
     → ⦃ Eq $ LL.e Bean ⦄
     → A → A → ℕ
dist a b = Data.List.length $ Data.List.filter drata ziprd
  where
  drata = _≟_ false ∘ isYes ∘ uncurry _≟_
  ziprd = Data.List.zip (lst a) $ lst b
    where
    lst = toList ∘ vec
\end{code}

\subsection{la'oi .\F{\AgdaUnderscore∈\AgdaUnderscore}.}
ni'o ga jo la'oi .\AgdaInductiveConstructor{refl}.\ ctaipe la'o zoi.\ \B a \OpF ∈ \B b .zoi.\ gi ga je su'o da zo'u da ctaipe la'o zoi.\ \F{Eq} \OpF \$ \F{typeOf} \B a .zoi.\ gi la'oi .\B b.\ se cmima la'oi .\B a.

\begin{code}
_∈_ : ∀ {a} → {A : Set a}
    → ⦃ Fireball : LL A ⦄
    → ⦃ Eq $ LL.e Fireball ⦄
    → LL.e Fireball → A → Set
_∈_ a = _≡_ 1 ∘ lengthₗ ∘ Data.List.take 1 ∘ filterₗ (_≟_ a) ∘ f
  where
  -- | .i cumki fa lo nu sruma lo du'u zo'oi .f.
  -- cmavlaka'i zo'oi .from... ja cu co'e
  f = toList ∘ vec
\end{code}

\subsection{la'o zoi.\ \F{\AgdaUnderscore∉\AgdaUnderscore}\ .zoi.}
ni'o ga jo la'oi .\AgdaInductiveConstructor{refl}.\ ctaipe la'o zoi.\ \B x \OpF ∉ \B y\ .zoi.\ gi la'o zoi.\ \B y\ .zoi.\ na se cmima la'o zoi.\ \B x\ .zoi.

\begin{code}
_∉_ : ∀ {a} → {Bean : Set a}
    → ⦃ Jeans : LL Bean ⦄ → ⦃ _ : Eq $ LL.e Jeans ⦄
    → LL.e Jeans → Bean → Set
_∉_ x = _≡_ 0 ∘ lengthₗ ∘ filterₗ (_≟_ x) ∘ toList ∘ vec
\end{code}

\subsection{la'oi .\F{\AgdaUnderscore{}∈₂\AgdaUnderscore}.}
ni'o ga jo ctaipe la'o zoi.\ \B a \AgdaOperator{\F{∈₂}} \B b\ .zoi.\ gi la'o zoi.\ \B a\ .zoi.\ cmima la'o zoi.\ \B b\ .zoi.

\begin{code}
_∈₂_ : ∀ {a} → {Bean : Set a}
     → ⦃ Jeans : LL Bean ⦄ → ⦃ _ : Eq $ LL.e Jeans ⦄
     → LL.e Jeans → Bean → Set a
_∈₂_ ⦃ Q ⦄ a b = DVRUA.Any (a ≡_) $ LL.vec Q b
\end{code}

\subsection{la'oi .\F{\AgdaUnderscore{}∈₂?\AgdaUnderscore}.}
ni'o xu sarcu fa lo nu la .varik.\ cu ciksi bau la .lojban.

\begin{code}
_∈₂?_ : ∀ {a} → {Bean : Set a}
       → ⦃ Jeans : LL Bean ⦄ → ⦃ _ : Eq $ LL.e Jeans ⦄
       → (x : LL.e Jeans) → (xs : Bean) → Dec $ x ∈₂ xs
_∈₂?_ ⦃ Q ⦄ x xs = DVRUA.any? (x ≟_) $ LL.vec Q xs
\end{code}

\subsubsection{la'oi .\F{\AgdaUnderscore{}∉₂\AgdaUnderscore}.}
ni'o ga jo ctaipe la'o zoi.\ \B a \AgdaOperator{\F{∉₂}} \B b\ .zoi.\ gi la'o zoi.\ \B a\ .zoi.\ na cmima la'o zoi.\ \B b\ .zoi.

\begin{code}
_∉₂_ : ∀ {a} → {Bean : Set a}
     → ⦃ Jeans : LL Bean ⦄ → ⦃ _ : Eq $ LL.e Jeans ⦄
     → LL.e Jeans → Bean → Set a
_∉₂_ ⦃ Q ⦄ a b = DVRUL.All (a ≢_) $ LL.vec Q b
\end{code}


\subsection{la'oi .\F{\AgdaUnderscore{}∉₂?\AgdaUnderscore}.}
ni'o xu sarcu fa lo nu la .varik.\ cu ciksi bau la .lojban.

\begin{code}
_∉₂?_ : ∀ {a} → {Bean : Set a}
       → ⦃ Jeans : LL Bean ⦄ → ⦃ _ : Eq $ LL.e Jeans ⦄
       → (x : LL.e Jeans) → (xs : Bean) → Dec $ x ∉₂ xs
_∉₂?_ ⦃ Q ⦄ x = DVRUL.all? (inv {P = x ≡_} ∘ _≟_ x) ∘ LL.vec Q
  where
  inv : ∀ {a p} → {A : Set a} → {P : Pred A p}
      → {x : A}
      → Dec $ P x
      → Dec $ ¬_ $ P x
  inv record {does = false; proof = ofⁿ x} = R
    where
    R = record {does = true; proof = ofʸ x}
  inv record {does = true; proof = ofʸ x} = R
    where
    R = record {does = false; proof = ofⁿ $ flip _$_ x}
\end{code}

\subsection{la'oi .\F{nu,iork}.}
ni'o ga jo ctaipe la'o zoi.\ \F{nu,iork} \B a .zoi.\ gi ro da poi ke'a selvau la'oi .\B a.\ zo'u li pa nilzilcmi lo'i ro co'e poi da meirmoi ke'a fo la'oi .\B a.

\begin{code}
nu,iork : ∀ {a} → {Bean : Set a}
        → ⦃ Q : LL Bean ⦄ → ⦃ Eq $ LL.e Q ⦄
        → Bean → Set a
nu,iork = nu,iork' ∘ Data.Vec.toList ∘ vec
  where
  nu,iork' = λ a → a ≡ filterₗ (λ b → []' b ≟ filterₗ (_≟_ b) a) a
    where
    []' = flip List._∷_ List.[]
\end{code}

\section{la'oi .\F{UL}.}
ni'o ga jo la'o zoi.\ \B A \OpF , \B b .zoi.\ ctaipe la'o zoi.\ zoi.\ \F{UL} \B A .zoi.\ gi ro da poi ke'a selvau ko'a goi la'oi .\B A.\ zo'u li pa du lo nilzilcmi be lo'i ro selvau be ko'a be'o poi ke'a du da

\begin{code}
UL : ∀ {a} → (A : Set a)
   → ⦃ L : LL A ⦄ → ⦃ Eq $ LL.e L ⦄
   → Set a
UL A = Σ A nu,iork
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

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
    vec = λ q → replicateᵥ {_} {_} {q} $ 𝔽.fromℕ 0;
    cev = Data.Vec.length}
\end{code}

\section{la'oi .\AgdaRecord{LC}.}
ni'o ga jo la'oi .\B Q.\ drani gi la'o zoi.\ \AgdaField{LC.\AgdaUnderscore++\AgdaUnderscore} \B Q \B a \B b .zoi.\ konkatena la'oi .\B a.\ la'oi .\B b.

\begin{code}
record LC {a} (A B : Set a) ⦃ Q : LL A ⦄ ⦃ R : LL B ⦄ : Set a
  where
  field
    _++_ : (C : A) → (D : B) → LL.olen Q $ LL.l Q C + LL.l R D
\end{code}

\subsection{le fancu}

\subsubsection{la'oi .\F{\AgdaUnderscore++\AgdaUnderscore}.}
ni'o la'o zoi.\ \B a \OpF{++} \B b .zoi.\ konkatena la'oi .\B a.\ la'oi .\B b.

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
\end{code}
\end{document}
