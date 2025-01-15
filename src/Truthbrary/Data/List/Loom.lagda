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
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}

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
	\noindent ni'o la'o zoi.\ \kulmodis\ .zoi.\ vasru lo velcki be lo ctaipe be lo su'u dunli be'o be'o je lo velcki be lo fancu ja co'e be ko'a goi lo liste bei zo'e ja lo liste poi su'o da zo'u da me'oi .\F{length}.\ ke'a je ko'a je poi su'o da zo'u lo meirmoi be da bei fo ke'a cu co'e ja frica lo meirmoi be da bei fo ko'a
\end{abstract}

\section{le torveki}
ni'o la .varik.\ na birti lo du'u ma kau xamgu torveki ko'a goi la'o zoi.\ \kulmodis\ .zoi.\ kei je cu curmi lo nu cusku lo se du'u cadga fa lo nu ma kau torveki ko'a

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Data.List.Loom where

open import Data.Fin
  as 𝔽
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
    _on_;
    flip;
    id;
    _∘_;
    _$_
  )
  renaming (
    _|>_ to _▹_
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
    minzero;
    mink
  )
open import Data.List.Properties
  using (
    length-map
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    subst;
    cong;
    refl;
    _≗_;
    _≡_;
    sym
  )

open ≡-Reasoning
  using (
    step-≡;
    begin_;
    _∎
  )
\end{code}

\section{la .\F{lum}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{lum}.\ bau la .lojban.

\begin{code}
lum : ∀ {a b} → {A : Set a} → {B : Set b}
    → (l : List A)
    → (f : A → B)
    → (n : Fin $ length l)
    → map f l ! mink n (sym $ length-map f l) ≡ f (l ! n)
lum (x ∷ xs) f zero = begin
  map f (x ∷ xs) ! (mink zero ℓ) ≡⟨ minzero ℓ ▹ cong x∷xs'! ⟩
  map f (x ∷ xs) ! zero ≡⟨ refl ⟩
  f x ∎
  where
  ℓ = sym $ length-map f $ x ∷ xs
  x∷xs'! = _!_ $ map f $ x ∷ xs
lum (x ∷ xs) f (suc n) = begin
  map f (x ∷ xs) ! mink (suc n) tryks ≡⟨ 𝔪 n tryk tryks ▹ kong ⟩
  map f (x ∷ xs) ! suc (mink n tryk) ≡⟨ refl ⟩
  map f xs ! mink n tryk ≡⟨ lum xs f n ⟩
  f (xs ! n) ∎
  where
  kong = cong $ _!_ $ map f $ x ∷ xs
  tryk = sym $ length-map f xs
  tryks = sym $ length-map f $ x ∷ xs
  𝔪 : {m n : ℕ}
    → (t : Fin m)
    → (x : m ≡ n)
    → (x₂ : suc m ≡ suc n)
    → mink (suc t) x₂ ≡ suc (mink t x)
  𝔪 t refl refl = refl
\end{code}

\section{la .\F{ual}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ual}.\ bau la .lojban.

\begin{code}
ual : ∀ {a} → {A : Set a}
    → (l : List A)
    → (n : Fin $ length l)
    → (f : A → A)
    → Σ (List A) $ λ l'
      → Σ (length l ≡ length l') $ λ ℓ
      → l' ! mink n ℓ ≡ f (l ! n)
ual (x ∷ xs) zero f = f x ∷ xs , refl , refl
ual (x ∷ xs) (suc n) f = x ∷ proj₁ u , r₂ , r₃
  where
  u = ual xs n f
  u₂ = u ▹ λ (v , x , z) → x
  r₂ = cong suc u₂
  r₃ = subst i (sukmi u₂) $ proj₂ $ proj₂ u
    where
    i = λ i → (x ∷ proj₁ u) ! i ≡ f ((x ∷ xs) ! suc n)
    sukmi : {m n : ℕ}
          → {f : Fin m}
          → (_≗_
              (suc ∘ mink f)
              (mink {n = suc n} (suc f) ∘ cong suc))
    sukmi refl = refl
\end{code}

\section{la .\F{ualmap}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualmap}.\ bau la .lojban.

\begin{code}
ualmap : ∀ {a b} → {A : Set a} → {B : Set b}
       → (x : List A)
       → (f : A → B)
       → (g : B → B)
       → (k : Fin $ length x)
       → Σ (List B) $ λ l
         → Σ (length x ≡ length l) $ λ ℓ
         → g (f $ x ! k) ≡ l ! mink k ℓ
ualmap {B = B} x f g k = proj₁ l , _ , sym p₃
  where
  mifix = map f x
  ℓ : length x ≡ length mifix
  ℓ = length-map f x ▹ sym
  k₂ = mink k ℓ
  l : Σ (List B) $ λ l
      → Σ _ $ λ ℓ
      → l ! mink k₂ ℓ ≡ g (mifix ! k₂)
  l = ual mifix k₂ g
  p₂ = begin
    length x ≡⟨ length-map f x ▹ sym ⟩
    length (map f x) ≡⟨ proj₁ $ proj₂ l ⟩
    length (proj₁ l) ∎
  p₃ = begin
    proj₁ l ! mink k p₂ ≡⟨ M k ℓ ℓ₂ xul ▹ cong (proj₁ l !_) ⟩
    proj₁ l ! mink k₂ (proj₁ $ proj₂ l) ≡⟨ proj₂ $ proj₂ l ⟩
    g (map f x ! k₂) ≡⟨ lum x f k ▹ cong g ⟩
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
    M _ refl refl refl = refl
\end{code}

\section{la .\F{ualkonk}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualkonk}.\ bau la .lojban.

\begin{code}
ualkonk : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = 𝔽.toℕ n in
          (_≡_
            (proj₁ $ ual x n f)
            (_++_
              (take n' x)
              (_∷_
                (f $ x ! n)
                (drop (suc n') x))))
ualkonk (_ ∷ _) zero _ = refl
ualkonk (_ ∷ _) (suc _) _ = ualkonk _ _ _ ▹ cong (_ ∷_) 
\end{code}

\section{la .\F{ualteik}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualteik}.\ bau la .lojban.

\begin{code}
ualteik : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = 𝔽.toℕ n in
          take n' x ≡ take n' (proj₁ $ ual x n f)
ualteik (_ ∷ _) zero _ = refl
ualteik (x ∷ xs) (Fin.suc n) = cong (_∷_ x) ∘ ualteik xs n
\end{code}

\section{la .\F{ualdrop}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualdrop}.\ bau la .lojban.

\begin{code}
ualdrop : ∀ {a} → {A : Set a}
        → (x : List A)
        → (n : Fin $ length x)
        → (f : A → A)
        → let n' = suc $ 𝔽.toℕ n in
          drop n' x ≡ drop n' (proj₁ $ ual x n f)
ualdrop (_ ∷ _) Fin.zero _ = refl
ualdrop (_ ∷ xs) (Fin.suc n) = ualdrop xs n
\end{code}

\section{la .\F{ualmapkonk}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{ualmapkonk}.\ bau la .lojban.

\begin{code}
ualmapkonk : ∀ {a} → {A B : Set a}
           → (x : List A)
           → (n : Fin $ length x)
           → (f : A → B)
           → (g : B → B)
           → let n' = 𝔽.toℕ n in
             (_≡_
               (proj₁ $ ualmap x f g n)
               (_++_
                 (take n' $ map f x)
                 (_∷_
                   (g $ f $ x ! n)
                   (drop (suc n') $ map f x))))
ualmapkonk x n f g = begin
  proj₁ (ualmap x f g n) ≡⟨ refl ⟩
  proj₁ (ual (map f x) n₂ g) ≡⟨ ualkonk (map f x) n₂ g ⟩
  t take n₂' ++ g ((map f x) ! n₂) ∷ t drop (suc n₂') ≡⟨ mynydus ⟩
  t take n' ++ g ((map f x) ! n₂) ∷ t drop (suc n') ≡⟨ lum x f n ▹ cong (p n') ⟩
  t take n' ++ g (f $ x ! n) ∷ t drop (suc n') ∎
  where
  n₂ = mink n $ length-map f x ▹ sym
  n₂' = 𝔽.toℕ n₂
  n' = 𝔽.toℕ n
  t = λ f₂ → flip f₂ $ map f x
  tondus : {m n : ℕ} → (d : m ≡ n) → 𝔽.toℕ ≗ (𝔽.toℕ ∘ flip mink d)
  tondus refl _ = refl
  p = λ n c → t take n ++ g c ∷ t drop (suc n)
  mynydus = tondus _ n ▹ sym ▹ cong (flip p $ map f x ! n₂)
\end{code}

\section{la .\F{teiklendus}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{teiklendus}.\ bau la .lojban.

.i zo .teiklendus.\ cmavlaka'i lo konkatena be zo'oi .take.\ bei zo'oi .length.\ bei zo dunli

\begin{code}
teiklendus : ∀ {a} → {A : Set a}
           → (x : List A)
           → (n : ℕ)
           → n ≤ length x
           → length (take n x) ≡ n
teiklendus _ 0 _ = refl
teiklendus (_ ∷ _) (suc _) (s≤s g) = cong suc t
  where
  t = teiklendus _ _ g
\end{code}

\section{la .\F{mapimplant}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi la .\F{mapimplant}.\ fo lo te gerna be fi la .lojban.

\begin{code}
mapimplant : ∀ {a b} → {A : Set a} → {B : Set b}
           → (x : List A)
           → (z : B)
           → (f : A → B)
           → (n : Fin $ length x)
           → let n' = 𝔽.toℕ n in
             let sin = suc n' in
             ((_≡_ on (λ (a ,  b) → a ++ z ∷ b))
               (take n' (map f x) , drop sin (map f x))
               (map f (take n' x) , map f (drop sin x)))
mapimplant (_ ∷ _) _ _ zero = refl
mapimplant (x ∷ xs) z f (suc _) = mip ▹ cong (f x ∷_)
  where
  mip = mapimplant xs _ _ _
\end{code}
\end{document}
