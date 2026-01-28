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
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∷}{\ensuremath{\mathnormal{\Colon}}}
\newunicodechar{∋}{\ensuremath{\mathnormal{\ni}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Data.Vec.Matrix}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\section{le torveki}
ni'o la'o zoi.\ \texttt{\cmene} .zoi.\ vasru\ldots
\begin{itemize}
	\item le velcki be la'o zoi.\ \F 𝕄 .zoi.\ noi tu'a ke'a filri'a tu'a lo nacmeimei be'o je
	\item le velcki be la'o zoi.\ \F{lookup} .zoi.\ noi tu'a ke'a filri'a tu'a lo pinpau ja co'e be lo nacmeimei ku'o be'o je
	\item le velcki be la'o zoi.\ \F I .zoi.\ noi tu'a ke'a filri'a tu'a lo me'oi .identity.\ nacmeimei be'o je
	\item le velcki be la'o zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.\ noi tu'a ke'a filri'a tu'a lo konkatena bei lo nacmeimei bei lo nacmeimei
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Truthbrary.Data.Vec.Matrix where

open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ;
    _+_
  )
open import Data.Vec
  renaming (
    lookup to lookupᵥ
  )
open import Function
open import Algebra.Core
  using (
    Op₂
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    cong;
    _≡_;
    sym
  )
open import Data.Vec.Properties
  as DVP
  using (
  )
\end{code}

\section{la'o zoi.\ \F 𝕄\ .zoi.}
ni'o ro da zo'u ga jo da ctaipe la'o zoi.\ \F 𝕄 \B A \B c \B b .zoi.\ gi da nacmeimei la'o zoi.\ \B b .zoi.\ la'o zoi.\ \B c .zoi.\ je cu vasru lo ctaipe be la'o zoi.\ \B A .zoi.

\subsection{le su'u me'oi .order.}
\newcommand\InductiveOperator[1]{\AgdaOperator{\AgdaInductiveConstructor{#1}}}
\newcommand\nacmeimeiPagbu[3]{\AgdaNumber{#1} \InductiveOperator ∷ \AgdaNumber{#2} \InductiveOperator ∷ \AgdaNumber{#3} \InductiveOperator ∷ \AgdaInductiveConstructor{[]}}
ni'o la'o zoi.\
\F 𝕄 \D ℕ \AgdaNumber 3 \AgdaNumber 3 \F ∋
	\Sym(\Sym(\nacmeimeiPagbu123\Sym) \InductiveOperator ∷
	     \Sym(\nacmeimeiPagbu456\Sym) \InductiveOperator ∷
	     \Sym(\nacmeimeiPagbu789\Sym) \InductiveOperator ∷
	     \AgdaInductiveConstructor{[]}\Sym)
.zoi.\ nacmeimei je cu du la'o cmaci.
\[
	\begin{bmatrix}
		1 & 2 & 3 \\
		4 & 5 & 6 \\
		7 & 8 & 9
	\end{bmatrix}
\]
.cmaci.

\subsection{le cimde}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \F 𝕄 \B A \B m \B m\ .zoi.\ zo'u ga je\ldots
\begin{itemize}
	\item la'oi .\B m.\ ni ganra co'e fa lo se sinxa be da gi
	\item la'oi .\B n.\ ni rajycla co'e fa lo se sinxa be da
\end{itemize}

\begin{code}
𝕄 : ∀ {a} → Set a → ℕ → ℕ → Set a
𝕄 = Vec ∘₂ Vec
\end{code}

\section{la'oi .\F{lookup}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la'oi .\F{lookup}.\ bau la .lojban.

\begin{code}
lookup : ∀ {a n o} → {A : Set a} → 𝕄 A n o → Fin n → Vec A o
lookup m n = map (flip lookupᵥ n) m
\end{code}

\section{la'oi .\F I.}
ni'o ga jo la'o zoi.\ \F I \Sym\{\AgdaUnderscore\Sym\} \Sym\{\B A\Sym\} \B z \B o .zoi.\ me'oi .identity.\ nacmeimei gi ro da poi ke'a ctaipe la'o zoi.\ \B A .zoi.\ zo'u ga je lo pilji ja co'e be da bei la'o zoi.\ \B z .zoi.\ du la'o zoi.\ \B z .zoi.\ gi da du lo pilji ja co'e be da bei la'o zoi.\ \B o .zoi.

\begin{code}
module I where
  I : ∀ {a} → {A : Set a} → {n : ℕ} → A → A → 𝕄 A n n
  I z o = map (λ x → updateAt x (const o) $ replicate z) $ allFin _
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
  module Veritas where
\end{code}

\begin{code}
    1≡n,n : ∀ {a} → {A : Set a}
          → (n : ℕ)
          → (f : Fin n)
          → (z o : A)
          → o ≡ lookupᵥ (lookupᵥ (I z o) f) f
    1≡n,n n f z o = sym $ begin
      lookupᵥ (lookupᵥ (I z o) f) f ≡⟨ _≡_.refl ⟩
      lookupᵥ (lookupᵥ (map fx $ allFin _) f) f ≡⟨ _≡_.refl ⟩
      _ ≡⟨ cong (λ x → lookupᵥ x f) $ sym d ⟩
      lookupᵥ (fx f) f ≡⟨ DVP.lookup∘updateAt f _ ⟩
      o ∎
      where
      fx = λ x → updateAt x (const o) $ replicate z
      open ≡-Reasoning
      d : (_≡_
            (fx f)
            (flip lookupᵥ
              f
              (map fx $ allFin _)))
      d = sym $ begin
        lookupᵥ (map fx $ allFin _) f ≡⟨ DVP.lookup-map f fx $ allFin _ ⟩
        fx (lookupᵥ (allFin _) f) ≡⟨ cong fx $ DVP.lookup∘tabulate id f ⟩
        fx f ∎
\end{code}

\begin{code}
    0≡n,n : ∀ {a} → {A : Set a}
          → (n : ℕ)
          → (f g : Fin n)
          → (z o : A)
          → ¬_ $ f ≡ g
          → z ≡ Data.Vec.lookup (lookup (I z o) f) g
    0≡n,n = λ n f g z o N → sym $ begin
      Data.Vec.lookup (lookup (I z o) f) g ≡⟨ {!!} ⟩
      z ∎
      where
      open ≡-Reasoning
\end{code}

\subsection{le co'e ja se me'oi .export.}
ni'o lo su'u cusku zo'e ja zoi zoi.\ \F{I.I}\ .zoi.\ cu milxe le ka ce'u jai fanza la .varik.  .i zo'e joi la'e di'u krinu le su'u la .varik.\ cu curmi tu'a zo'oi .\F I.

\begin{code}
I = I.I
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \AgdaOperator{\F{∣}} \B b .zoi.\ konkatena la'o zoi.\ \B a .zoi.\ la'o zoi.\ \B b .zoi.  .i mupli fa le su'u ga jo ga je da se sinxa zoi zoi.\

\[
	\begin{bmatrix}
		1 & 2 & 3 \\
		4 & 5 & 6 \\
	\end{bmatrix}
\]

.zoi.\ gi de se sinxa zoi zoi.\

\[
	\begin{bmatrix}
		1 \\
		4 \\
	\end{bmatrix}
\]

.zoi.\ gi lo mu'oi zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.\ be da bei de cu se sinxa zoi zoi.\

\[
	\begin{bmatrix}
		1 & 2 & 3 & 1 \\
		4 & 5 & 6 & 4 \\
	\end{bmatrix}
\]

.zoi.

\begin{code}
module _∣_ where
  _∣_ : ∀ {a} → {A : Set a} → {m n o : ℕ}
      → 𝕄 A m n → 𝕄 A o n → 𝕄 A (m + o) n
  _∣_ a b = map (λ n → lookupᵥ a n ++ lookupᵥ b n) $ allFin _
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
  module Veritas where
    ind : ∀ {a} → {A : Set a}
        → {m n o : ℕ}
        → (x₁ : 𝕄 A m n)
        → (x₂ : 𝕄 A o n)
        → (i : Fin n)
        → lookupᵥ (x₁ ∣ x₂) i ≡ (lookupᵥ x₁ i ++ lookupᵥ x₂ i)
    ind x₁ x₂ i = begin
      lookupᵥ (x₁ ∣ x₂) i ≡⟨ _≡_.refl ⟩
      lookupᵥ (map L $ allFin _) i ≡⟨ DVP.lookup-map i L (allFin _) ⟩
      L (lookupᵥ (tabulate id) i) ≡⟨ cong L $ DVP.lookup∘tabulate id i ⟩
      L i ≡⟨ _≡_.refl ⟩
      (lookupᵥ x₁ i ++ lookupᵥ x₂ i) ∎
      where
      L = λ n → lookupᵥ x₁ n ++ lookupᵥ x₂ n
      open ≡-Reasoning
\end{code}

\subsection{le co'e ja se me'oi .export.}
ni'o lo su'u cusku zo'e ja zoi zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore.\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.\ cu milxe le ka ce'u jai fanza la .varik.  .i zo'e joi la'e di'u krinu le su'u la .varik.\ cu curmi tu'a zoi zoi.\ \F{\AgdaUnderscore∣\AgdaUnderscore}\ .zoi.

\begin{code}
_∣_ = _∣_._∣_
\end{code}
\end{document}
