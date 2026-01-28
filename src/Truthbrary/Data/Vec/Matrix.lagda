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
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{⁻}{\ensuremath{\mathnormal{{}^-}}}
\newunicodechar{¹}{\ensuremath{\mathnormal{{}^1}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{{}_m}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{{}_n}}}

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
open import Data.Vec.Properties
  as DVP
  using (
  )
open import Relation.Binary.PropositionalEquality
  as ≡
  using (
    sym;
    _≡_
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

\section{le fancu fancu}

\subsection{le pa moi}
ni'o ro da poi ke'a ctaipe zo'e zo'u ro ny xi pa oi ke'a ctaipe zo'e zo'u ro ny xi re poi ke'a ctaipe zo'e zo'u lo co'e ja meirmoi be ny xi pa pi'e ny xi re bei fo lo se sinxa be lo me'oi .\F{ff}.\ be da cu du lo me da be ny xi pa bei ny xi re

.i la'oi .\F{ff}.\ me'oi .inverse.\ la'o zoi.\ \F{ff⁻¹}\ .zoi.

\begin{code}
ff : ∀ {a} → {A : Set a} → {m n : ℕ}
   → (Fin m → Fin n → A)
   → 𝕄 A m n
ff f = map (λ x → map (flip f x) $ allFin _) $ allFin _
\end{code}

\subsection{le re moi}
ni'o ro da poi ke'a ctaipe zo'e zo'u ro ny xi pa oi ke'a ctaipe zo'e zo'u ro ny xi re poi ke'a ctaipe zo'e zo'u lo co'e ja meirmoi be ny xi pa pi'e ny xi re bei fo lo se sinxa be da cu du lo mu'oi zoi.\ \F{ff⁻¹}\ .zoi.\ be da bei ny xi pa bei ny xi re

.i la'o zoi.\ \F{ff⁻¹}\ .zoi.\ me'oi .inverse.\ la'oi .\F{ff}.

\begin{code}
ff⁻¹ : ∀ {a} → {A : Set a} → {m n : ℕ}
     → 𝕄 A m n
     → Fin m
     → Fin n
     → A
ff⁻¹ M = flip $ lookupᵥ ∘ lookupᵥ M
\end{code}

\subsection{le ctaipe be le su'u mapti}

\subsubsection{le ctaipe be le su'u me'oi .inverse.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la'o zoi.\ \F{ff∘ff⁻¹}\ .zoi.\ fo lo su'o te gerna be la .lojban.\sds  .i sa'u nai ru'e la .varik.\ cu jinvi le du'u le se ctaipe be cu banzuka le ka ce'u jai .indika kei le ka na sarcu lo nu jimpe fi ko'a goi le ctaipe be ce'u fa lo nu ciksi ko'a fo lo te gerna be la .lojban.

\begin{code}
ff∘ff⁻¹ : ∀ {a} → {A : Set a} → {m n : ℕ}
        → (M : 𝕄 A m n)
        → M ≡ ff (ff⁻¹ M)
ff∘ff⁻¹ M = sym $ begin
  ff (ff⁻¹ M) ≡⟨ ≡.refl ⟩
  map (λ x → map (flip (ff⁻¹ M) x) F) F ≡⟨ ≡.refl ⟩
  map (λ x → map (lookupᵥ $ lookupᵥ M x) F) F ≡⟨ DVP.map-cong (DVP.map-lookup-allFin ∘ lookupᵥ M) F ⟩
  map (lookupᵥ M) F ≡⟨ DVP.map-lookup-allFin M ⟩
  M ∎
  where
  F : {n : ℕ} → Vec (Fin n) n
  F = allFin _
  open ≡.≡-Reasoning
\end{code}

\subsubsection{le re moi be le'i ctaipe be le su'u me'oi .inverse.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
ff⁻¹∘ff : ∀ {a} → {A : Set a} → {m n : ℕ}
       → (g : Fin m → Fin n → A)
       → (fₘ : Fin m)
       → (fₙ : Fin n)
       → (_≡_
           (g fₘ fₙ)
           (ff⁻¹ (ff g) fₘ fₙ))
ff⁻¹∘ff = {!!}
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
I : ∀ {a} → {A : Set a} → {n : ℕ} → A → A → 𝕄 A n n
I z o = map (λ x → updateAt x (const o) $ replicate z) $ allFin _
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
_∣_ : ∀ {a} → {A : Set a} → {m n o : ℕ}
    → 𝕄 A m n → 𝕄 A o n → 𝕄 A (m + o) n
_∣_ a b = map (λ n → lookupᵥ a n ++ lookupᵥ b n) $ allFin _
\end{code}
\end{document}
