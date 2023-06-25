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
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{∎}{\ensuremath{\mathnormal{\blacksquare}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal{\langle}}}
\newunicodechar{⟩}{\ensuremath{\mathnormal{\rangle}}}
\newunicodechar{𝔦}{\ensuremath{\mathfrak{i}}}
\newunicodechar{𝔪}{\ensuremath{\mathfrak{m}}}
\newunicodechar{𝔭}{\ensuremath{\mathfrak{p}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\kulmodis{\texttt{Truthbrary.Data.List.Loom}}

\title{la'o zoi.\ \kulmodis\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
	\noindent ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru lo velcki be lo ctaipe be lo su'u dunli be'o be'o je lo velcki be lo fancu ja co'e be ko'a goi lo liste bei zo'e ja lo liste poi ga je lo me'oi .\F{length}.\ be ke'a cu du lo me'oi .\F{length}.\ be ko'a gi su'o da zo'u lo meirmoi be da bei fo ke'a cu frica ja co'e cu co'e lo meirmoi be da bei fo ko'a
\end{abstract}

\section{le torveki}
ni'o la .varik.\ cu na birti lo du'u ma kau xamgu torveki ko'a goi la'o zoi.\ \kulmodis\ .zoi.\ je cu curmi lo nu cusku lo se du'u cadga fa lo nu ma kau torveki ko'a

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.List.Loom where

open import Data.Fin
  using (
    Fin;
    suc;
    zero
  )
open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    id;
    _$_
  )
open import Data.List
  renaming (
    lookup to _!_
  )
open import Data.Product
  using (
    proj₁;
    proj₂;
    _,_;
    Σ
  )
open import Data.List.Properties
  using (
    length-map
  )
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
\end{code}

\section{le me'oi .\AgdaKeyword{private}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi le me'oi .\AgdaKeyword{private}.

\begin{code}
private
  mink : {m n : ℕ} → Fin n → n ≡ m → Fin m
  mink f refl = f
\end{code}

\section{la .\F{lum}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{lum}.\ bau la .lojban.

\begin{code}
lum : ∀ {a b} → {A : Set a} → {B : Set b}
    → (l : List A)
    → (f : A → B)
    → (n : Fin $ length l)
    → (map f l ! mink n (sym $ length-map f l)) ≡ f (l ! n)
lum (x ∷ xs) f zero = begin
  map f (x ∷ xs) ! (mink zero ℓ) ≡⟨ cong x∷xs! $ zil ℓ ⟩
  map f (x ∷ xs) ! zero ≡⟨⟩
  f x ∎
  where
  ℓ = sym $ length-map f $ x ∷ xs
  x∷xs! = _!_ $ map f $ x ∷ xs
  zil : {m n : ℕ}
      → (x : ℕ.suc m ≡ ℕ.suc n)
      → mink zero x ≡ zero
  zil refl = refl
lum (x ∷ xs) f (suc n) = begin
  map f (x ∷ xs) ! mink (suc n) tryks ≡⟨ kong $ 𝔪 n tryk tryks ⟩
  map f (x ∷ xs) ! suc (mink n tryk) ≡⟨ 𝔦 x xs f $ mink n tryk ⟩
  map f xs ! mink n tryk ≡⟨ lum xs f n ⟩
  f (xs ! n) ∎
  where
  kong = cong $ _!_ $ map f $ x ∷ xs
  tryk = sym $ length-map f xs
  tryks = sym $ length-map f $ x ∷ xs
  𝔪 : {m n : ℕ}
    → (t : Fin m)
    → (x : m ≡ n)
    → (d : ℕ.suc m ≡ ℕ.suc n)
    → mink (suc t) d ≡ suc (mink t x)
  𝔪 t refl refl = refl
  𝔦 : ∀ {a b} → {A : Set a} → {B : Set b}
    → (x : A)
    → (xs : List A)
    → (f : A → B)
    → (n : Fin $ length $ map f xs)
    → map f (x ∷ xs) ! (suc n) ≡ map f xs ! n
  𝔦 x xs f n = refl
\end{code}

\section{la .\F{ual}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ual}.\ bau la .lojban.

\begin{code}
ual : ∀ {a} → {A : Set a}
    → (l : List A) → (n : Fin $ length l) → (f : A → A)
    → Σ (List A) $ λ l'
      → Σ (length l ≡ length l') $ λ ℓ
      → l' ! mink n ℓ ≡ f (l ! n)
ual (x ∷ xs) zero f = f x ∷ xs , refl , refl
ual (x ∷ xs) (suc n) f = x ∷ proj₁ r₁ , r₂ , r₃
  where
  r₁ = ual xs n f
  r₂ = cong ℕ.suc $ proj₁ $ proj₂ r₁
  r₃ = i misuk $ p (proj₁ r₁) x $ proj₂ $ proj₂ r₁
    where
    p : ∀ {a} → {A : Set a}
      → {x : A}
      → (l : List A)
      → {n : Fin $ length l}
      → (z : A)
      → l ! n ≡ x
      → (z ∷ l) ! suc n ≡ x
    p l z = id
    i : ∀ {a} → {A : Set a}
      → {l : List A}
      → {m n : Fin $ length l}
      → {k : A}
      → m ≡ n
      → l ! m ≡ k
      → l ! n ≡ k
    i refl = id
    misuk : suc (mink n $ proj₁ $ proj₂ r₁) ≡ mink (suc n) r₂
    misuk = sukmi n $ proj₁ $ proj₂ r₁
      where
      sukmi : {m n : ℕ}
            → (f : Fin m)
            → (x : m ≡ n)
            → suc (mink f x) ≡ mink (suc f) (cong ℕ.suc x)
      sukmi f refl = refl
\end{code}

\section{la .\F{ualmap}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualmap}.\ bau la .lojban.

\begin{code}
ualmap : ∀ {a} → {A B : Set a}
       → (x : List A)
       → (f : A → B)
       → (g : B → B)
       → (k : Fin $ length x)
       → Σ (List B) $ λ l
         → Σ (length x ≡ length l) $ λ ℓ
         → g (f $ x ! k) ≡ l ! mink k ℓ
ualmap {_} {_} {B} x f g k = proj₁ l , p₂ , sym p₃
  where
  mifix = map f x
  ℓ : length x ≡ length mifix
  ℓ = sym $ length-map f x
  k₂ = mink k ℓ
  l : Σ (List B) $ λ l'
      → Σ (length mifix ≡ length l') $ λ ℓ
      → l' ! mink k₂ ℓ ≡ g (mifix ! k₂)
  l = ual mifix k₂ g
  p₂ = begin
    length x ≡⟨ sym $ length-map f x ⟩
    length (map f x) ≡⟨ proj₁ $ proj₂ l ⟩
    length (proj₁ l) ∎
  p₃ = begin
    proj₁ l ! mink k p₂ ≡⟨ cong (_!_ $ proj₁ l) $ M k ℓ ℓ₂ xul ⟩
    proj₁ l ! mink k₂ (proj₁ $ proj₂ l) ≡⟨ proj₂ $ proj₂ l ⟩
    g (map f x ! k₂) ≡⟨ cong g $ lum x f k ⟩
    g (f $ x ! k) ∎
    where
    ℓ₂ = proj₁ $ proj₂ l
    xul = begin
      length x ≡⟨ ℓ ⟩
      length (map f x) ≡⟨ ℓ₂ ⟩
      length (proj₁ l) ∎
    M : {l m n : ℕ}
      → (k : Fin l)
      → (v : l ≡ m)
      → (x : m ≡ n)
      → (xov : l ≡ n)
      → mink k xov ≡ mink (mink k v) x
    M k refl refl refl = refl
\end{code}
\end{document}
