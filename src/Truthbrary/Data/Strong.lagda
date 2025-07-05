\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\Xr[2]{\textrm{#1(#2)}}
\newcommand\datnyveicme\texttt

\title{la'o zoi.\ \datnyveicme{Truthbrary.Data.Strong}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
ni'o skicu bau la'oi .Agda.\ fe ko'a goi la'oi .\F{Strong}.\ noi ke'a smimlu ko'e goi la'o zoi.\ \AgdaPostulate{Data.String.String}\ .zoi.\ po la'o zoi.\ agda-stdlib .zoi.\ je ku'i cu zmadu fi le ka ce'u jai filri'a tu'a lo ctaipe\ldots ku'o ge'u je lo fancu pe ko'a\sds  .i troci lo nu frili fa lo nu basygau pe'a lo ctaipe pe ko'e lo ctaipe pe ko'a
\end{abstract}

\section{le vrici}

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\begin{code}
module Truthbrary.Data.Strong where
\end{code}

\begin{code}
open import Function
  using (
    _∘_;
    _$_;
    id
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Bool
  using (
    _∧_
  )
  renaming (
    if_then_else_ to if
  )
open import Data.List
  as 𝕃
  using (
    List
  )
  renaming (
    reverse to ⌽
  )
open import Data.Char
  using (
    Char
  )
open import Data.Empty
  using (
    ⊥
  )
open import Relation.Unary
  using (
    Decidable
  )
open import Relation.Nullary
  using (
    yes;
    no
  )
open import Data.List.Properties
  as DLP
  using (
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_
  )
open import Truthbrary.Record.LLC
  using (
    _∉_
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Nullary.Decidable
  using (
    isYes
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≗_;
    _≡_
  )

import Data.String as 𝕊
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
\end{code}

\section{la'oi .\F{Strong}.}
ni'o ko'a goi la'oi .\F{Strong}.\ smimlu la'o zoi.\ \AgdaPostulate{Data.String.String}\ .zoi.\ po la'o zoi.\ agda-stdlib\ .zoi.\ldots noi ku'i la .varik.\ cu tolnei tu'a lo ctaipe pe ke'a ki'u le su'u ke'a me'oi .\AgdaKeyword{postulate}.\ldots ku'o le ka ce'u ctaipe zo'e je lo se tcidu

\begin{code}
Strong : Set
Strong = List Char
\end{code}

\section{le mapti fancu}

\begin{code}
toList : Strong → List Char
toList = id
\end{code}

\begin{code}
fromList : List Char → Strong
fromList = id
\end{code}

\section{la'oi .\F{unwords}.}

\begin{code}
unwords : List Strong → Strong
unwords x = 𝕃.concat $ 𝕃.intersperse 𝕃.[ ' ' ] x
\end{code}

\section{la'oi .\F{words}.}
ni'o la .varik.\ na birti lo du'u ma kau zabna velcki je cu te gerna la .lojban.

\begin{code}
module words where
  soi : ∀ {a b} → {A : Set a} → {B : A → Set b}
      → List $ List A
      → List A
      → Decidable B
      → List A
      → List $ List A
  soi buf 𝕃.[] s 𝕃.[] = 𝕃.reverse buf
  soi buf c s 𝕃.[] = 𝕃.reverse $ c 𝕃.∷ buf
  soi buf c s (x 𝕃.∷ xs) = if (isYes $ s x) S K
    where
    S = soi (c 𝕃.∷ buf) 𝕃.[] s xs
    K = soi buf (c 𝕃.++ 𝕃.[ x ]) s xs

  soi₁ : ∀ {a b} → {A : Set a} → {B : A → Set b}
       → Decidable B
       → List A
       → List $ List A
  soi₁ = soi 𝕃.[] 𝕃.[]

  splitOn' : Char → Strong → List Strong
  splitOn' = soi₁ ∘ _≟_

  {-# TERMINATING #-}
  dedup' : ∀ {a} → {A : Set a}
         → ⦃ Truthbrary.Record.Eq.Eq A ⦄
         → List A
         → List A
         → List A
         → List A
  dedup' x b 𝕃.[] = x
  dedup' x b z = if ((z₁ ≡ᵇ b) ∧ (x' ≡ᵇ b)) d j
    where
    z₁ = 𝕃.take (𝕃.length b) z
    d = dedup' x b $ 𝕃.drop (𝕃.length b) z
    j = dedup' (x 𝕃.++ 𝕃.take 1 z) b $ 𝕃.drop 1 z
    x' = ⌽ $ 𝕃.take (𝕃.length b) $ ⌽ x

  {-# TERMINATING #-}
  dedup : ∀ {a} → {A : Set a}
        → ⦃ Truthbrary.Record.Eq.Eq A ⦄
        → List A
        → List A
        → List A
  dedup = dedup' 𝕃.[]

  words : Strong → List Strong
  words = splitOn' ' ' ∘ dedup 𝕃.[ ' ' ]

  module Veritas where
    module dedup where
      dxx : ∀ {a} → {A : Set a}
          → ⦃ _ : Truthbrary.Record.Eq.Eq A ⦄
          → (x : List A)
          → x ≡ dedup x x
      dxx = {!!}

      sampu : ∀ {a} → {A : Set a}
            → ⦃ _ : Truthbrary.Record.Eq.Eq A ⦄
            → (n : ℕ)
            → (x : List A)
            → (_≡_
                x
                (dedup
                  x
                  (𝕃.concat $ 𝕃.replicate (ℕ.suc n) x)))
      sampu 0 x = sym $ begin
        dedup x (𝕃.concat $ 𝕃.replicate 1 x) ≡⟨ cong (dedup x) $ cr x ⟩
        dedup x x ≡⟨ sym $ dxx x ⟩
        x ∎
        where
        open import Relation.Binary.PropositionalEquality
        open ≡-Reasoning
        cr : ∀ {a} → {A : Set a}
           → (x : List A)
           → 𝕃.concat (𝕃.replicate 1 x) ≡ x
        cr x = begin
          𝕃.concat (𝕃.replicate 1 x) ≡⟨ refl ⟩
          𝕃.concat 𝕃.[ x ] ≡⟨ refl ⟩
          x 𝕃.++ 𝕃.[] ≡⟨ DLP.++-identityʳ x ⟩
          x ∎
      sampu (ℕ.suc n) x = sym $ begin
        dedup x (𝕃.concat $ 𝕃.replicate (ℕ.suc $ ℕ.suc n) x) ≡⟨ {!!} ⟩
        dedup x (x 𝕃.++ 𝕃.concat (𝕃.replicate (ℕ.suc n) x)) ≡⟨ {!!} ⟩
        x ∎
        where
        open import Relation.Binary.PropositionalEquality
        open ≡-Reasoning

      dun : ∀ {a} → {A : Set a}
          → ⦃ _ : Truthbrary.Record.Eq.Eq A ⦄
          → (x : List A)
          → (d : List A)
          → (_ : (lt ld r : ℕ)
               → (_≡_
                   (𝕃.take lt $ 𝕃.drop ld x)
                   (𝕃.concat $ 𝕃.replicate (ℕ.suc r) d))
               → ⊥)
          → x ≡ dedup d x
      dun = {!!}

    module soi where
      sxs : (o : List Strong)
          → (buf ss : Strong)
          → (x : Char)
          → let f = x ≟_ in
            (_≡_
              (soi o buf f $ x 𝕃.∷ ss)
              (soi (buf 𝕃.∷ o) 𝕃.[] f ss))
      sxs = {!!}

    nocan : (x : Strong) → 𝕃.All (' ' ∉_) $ words x
    nocan = {!!}

    konk : dedup 𝕃.[ ' ' ] ≗ (unwords ∘ words)
    konk = {!!}

    kons : (x₁ x₂ : Strong)
         → (n : ℕ)
         → (_≡_
             (words $ x₁ 𝕃.++ 𝕃.[ ' ' ] 𝕃.++ x₂)
             (words
               ((λ x → x₁ 𝕃.++ x 𝕃.++ x₂)
                 (𝕃.replicate (ℕ.suc n) ' '))))
    kons = {!!}

words : Strong → List Strong
words = words.words
\end{code}

\section{la'oi .\F{lines}.}
ni'o ga je ro da poi ke'a cmima pe'a la'o zoi.\ \F{words} \B{x}\ .zoi.\ zo'u lo no lerpinsle bitmu lerfu lerfu cu cmima pe'a da gi la'oi .\B x.\ du la'o zoi.\ \F{𝕃.concat} \OpF{\$} \F{𝕃.intersperse} \OpF{𝕃.[} \AgdaString{'\textbackslash{}n'} \OpF{]} \OpF{\$} \F{words} \AgdaBound{x}\ .zoi.

\begin{code}
lines : Strong → List Strong
lines = words.splitOn' '\n'
\end{code}

\section{la'oi .\F{unlines}.}
ni'o ro da zo'u ro de zo'u lo meirmoi be de bei fo da cu meirmoi de fo lo'i ro lerpinsle pe lo me'oi .\F{unlines}.\ be da

\begin{code}
unlines : List Strong → Strong
unlines = 𝕃.concat ∘ 𝕃.intersperse 𝕃.[ '\n' ]
\end{code}
\end{document}
