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
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
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

% | ni'o la .varik. na morji lo du'u cmene ki'u ma
%
% .i ku'i xajmi la .varik.
\newcommand\kulmodis{\texttt{Truthbrary.Data.List.Loom}}

\title{la'o zoi.\ \kulmodis\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
	\noindent ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru lo velcki be lo ctaipe be lo su'u dunli be'o be'o je lo velcki be lo fancu ja co'e be ko'a goi lo liste bei zo'e ja lo liste poi su'o da zo'u da me'oi .\F{length}.\ ke'a je ko'a je poi su'o da zo'u lo meirmoi be da bei fo ke'a cu frica ja co'e lo meirmoi be da bei fo ko'a
\end{abstract}

\section{le torveki}
ni'o la .varik.\ na birti lo du'u ma kau xamgu torveki ko'a goi la'o zoi.\ \kulmodis\ .zoi.\ kei je cu curmi lo nu cusku lo se du'u cadga fa lo nu ma kau torveki ko'a

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
    suc;
    _≤_;
    s≤s;
    ℕ
  )
open import Function
  using (
    flip;
    id;
    _∘_;
    _$_
  )
open import Data.List
  using (
    length;
    _++_;
    List;
    take;
    drop;
    map;
    _∷_
  )
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
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Data.List.Properties
  using (
    length-map
  )
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
\end{code}

\section{la .\F{lum}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{lum}.\ bau la .lojban.

\begin{code}
lum : ∀ {a b} → {A : Set a} → {B : Set b}
    → (l : List A)
    → (f : A → B)
    → (n : Fin $ length l)
    → (map f l ! mink n (sym $ length-map f l)) ≡ f (l ! n)
lum (x ∷ xs) f zero = begin
  map f (x ∷ xs) ! (mink zero ℓ) ≡⟨ cong x∷xs'! $ zil ℓ ⟩
  map f (x ∷ xs) ! zero ≡⟨⟩
  f x ∎
  where
  ℓ = sym $ length-map f $ x ∷ xs
  x∷xs'! = _!_ $ map f $ x ∷ xs
  zil : {m n : ℕ}
      → (x : ℕ.suc m ≡ ℕ.suc n)
      → mink zero x ≡ zero
  zil = Truthbrary.Data.Fin.minzero
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
ualmap : ∀ {a b} → {A : Set a} → {B : Set b}
       → (x : List A)
       → (f : A → B)
       → (g : B → B)
       → (k : Fin $ length x)
       → Σ (List B) $ λ l
         → Σ (length x ≡ length l) $ λ ℓ
         → g (f $ x ! k) ≡ l ! mink k ℓ
ualmap {B = B} x f g k = proj₁ l , p₂ , sym p₃
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

\section{la .\F{ualkonk}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualkonk}.\ bau la .lojban.

\begin{code}
ualkonk : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = Data.Fin.toℕ n in
          (_≡_
            (proj₁ $ ual x n f)
            (_++_
              (take n' x)
              (_∷_
                (f $ x ! n)
                (drop (ℕ.suc n') x))))
ualkonk (_ ∷ _) Fin.zero _ = refl
ualkonk (x ∷ xs) (Fin.suc n) f = cong (_∷_ x) u
  where
  u = ualkonk xs n f
\end{code}

\section{la .\F{ualteik}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualteik}.\ bau la .lojban.

\begin{code}
ualteik : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = Data.Fin.toℕ n in
          take n' x ≡ take n' (proj₁ $ ual x n f)
ualteik (_ ∷ _) Fin.zero _ = refl
ualteik (x ∷ xs) (Fin.suc n) = cong (_∷_ x) ∘ ualteik xs n
\end{code}

\section{la .\F{ualdrop}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualdrop}.\ bau la .lojban.

\begin{code}
ualdrop : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = ℕ.suc $ Data.Fin.toℕ n in
          drop n' x ≡ drop n' (proj₁ $ ual x n f)
ualdrop (_ ∷ _) Fin.zero _ = refl
ualdrop (_ ∷ xs) (Fin.suc n) = ualdrop xs n
\end{code}

\section{la .\F{ualmapkonk}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualmapkonk}.\ bau la .lojban.

\begin{code}
ualmapkonk : ∀ {a} → {A B : Set a}
           → (x : List A)
           → (n : Fin $ length x)
           → (f : A → B)
           → (g : B → B)
           → let n' = Data.Fin.toℕ n in
             (_≡_
               (proj₁ $ ualmap x f g n)
               (_++_
                 (take n' $ map f x)
                 (_∷_
                   (g $ f $ x ! n)
                   (drop (ℕ.suc n') $ map f x))))
ualmapkonk x n f g = begin
  proj₁ (ualmap x f g n) ≡⟨ refl ⟩
  proj₁ (ual (map f x) m g) ≡⟨ ualkonk (map f x) m g ⟩
  t m' ++ g ((map f x) ! m) ∷ d (ℕ.suc m') ≡⟨ mynydus ⟩
  t n' ++ g ((map f x) ! m) ∷ d (ℕ.suc n') ≡⟨ midju ⟩
  t n' ++ g (f $ x ! n) ∷ d (ℕ.suc n') ∎
  where
  m = mink n $ sym $ length-map f x
  m' = Data.Fin.toℕ m
  n' = Data.Fin.toℕ n
  t = flip take $ map f x
  d = flip drop $ map f x
  tondus : {m n : ℕ}
         → (x : Fin m)
         → (d : m ≡ n)
         → Data.Fin.toℕ x ≡ Data.Fin.toℕ (mink x d)
  tondus _ refl = refl
  mynydus = cong p $ sym $ tondus n $ sym $ length-map f x
    where
    p = λ n → t n ++ g ((map f x) ! m) ∷ d (ℕ.suc n)
  midju = cong (λ c → t n' ++ g c ∷ d (ℕ.suc n')) $ lum x f n
\end{code}

\section{la .\F{teiklendus}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{teiklendus}.\ bau la .lojban.

.i zo .teiklendus.\ cmavlaka'i lo konkatena be zo'oi .take.\ bei zo'oi .length.\ bei zo dunli

\begin{code}
teiklendus : ∀ {a} → {A : Set a}
           → (xs : List A)
           → (n : ℕ)
           → n ≤ length xs
           → length (take n xs) ≡ n
teiklendus _ 0 _ = refl
teiklendus (_ ∷ xs) (suc n) (s≤s g) = cong ℕ.suc t
  where
  t = teiklendus xs n g
\end{code}

\section{la .\F{mapimplant}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu ciksi la .\F{mapimplant}.\ bau la .lojban.

\begin{code}
mapimplant : ∀ {a b} → {A : Set a} → {B : Set b}
           → (x : List A)
           → (z : B)
           → (f : A → B)
           → (n : Fin $ length x)
           → let n' = Data.Fin.toℕ n in
             let sin = ℕ.suc n' in
             (_≡_
               (take n' (map f x) ++ z ∷ drop sin (map f x))
               (map f (take n' x) ++ z ∷ map f (drop sin x)))
mapimplant (_ ∷ _) _ _ zero = refl
mapimplant (x ∷ xs) z f (suc n) = cong (_∷_ $ f x) mip
  where
  mip = mapimplant xs z f n
\end{code}
\end{document}
