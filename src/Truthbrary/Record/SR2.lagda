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
\newunicodechar{𝕍}{\ensuremath{\mathnormal{\mathbb V}}}
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
\newunicodechar{ˢ}{\ensuremath{\mathnormal{^\AgdaFontStyle{s}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{₄}{\ensuremath{\mathnormal{_4}}}
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
\newunicodechar{？}{\ensuremath{\texttt{?}}}

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

\title{la'o zoi.\ \datnyveicme{Truthbrary.Record.SR2}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{code}
module Truthbrary.Record.SR2 where

open import Level
  using (
    _⊔_;
    suc
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    _⊎_
  )
open import Data.Vec
  as 𝕍
  using (
    Vec
  )
open import Function
  using (
    _∘_;
    _ˢ_;
    _$_
  )
  renaming (
    _|>_ to _▹_
  )
open import Data.Bool
  using (
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
open import Data.Maybe
  as ？
  using (
    to-witness;
    Is-nothing;
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Data.Integer
  as ℤ
  using (
    ℤ
  )
open import Data.Product
  as Σ
  using (
    proj₂;
    proj₁;
    _×_;
    _,_;
    Σ
  )
open import Data.Rational
  as ℚ
  using (
    ℚ
  )
open import Relation.Unary
  using (
    Decidable;
    _⊆_
  )
open import Data.Nat.DivMod
  as ℕ
  using (
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Data.Fin.Patterns
  as 𝔽
  using (
  )
open import Data.Nat.Properties
  as DNP
  using (
  )
open import Data.Nat.Coprimality
  as OCP
  using (
    Coprime
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Relation.Nullary.Decidable
  using (
    from-yes;
    isYes
  )
open import Data.List.Relation.Unary.All
  as 𝕃All
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    subst;
    cong;
    _≡_
  )

import Data.String
import Data.Maybe.Relation.Unary.Any
  as DMRN

module apDec where
  apDec' : ∀ {a b p}
         → {A : Set a} → {B : Set b}
         → {P : A → Set p}
         → (f : (x : A) → P x → B)
         → (x : A)
         → Dec $ P x
         → Maybe B
  apDec' f x = ？.map (f x) ∘ ？.decToMaybe

  apDec : ∀ {a b p}
        → {A : Set a} → {B : Set b}
        → {P : A → Set p}
        → ((x : A) → P x → B)
        → Decidable P
        → A
        → Maybe B
  apDec f = apDec' f ˢ_

apDec = apDec.apDec

record Read {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    P : Strong → Set p
    read : (x : Strong) → P x → A

record ReadMaybe {a p} (A : Set a) : Set (a ⊔ suc p)
  where
  field
    rr : Read {p = p} A
    P? : Decidable $ Read.P rr

  open Read rr

  readMaybe = apDec read P?

  justys : P ⊆ (Is-just ∘ readMaybe)
  nad : (¬_ ∘ P) ⊆ (Is-nothing ∘ readMaybe)

  justys = J⇒IJ _ _ ∘ dij _
    where
    J⇒IJ : ∀ {a} → {A : Set a}
         → (x : Maybe A)
         → (z : A)
         → x ≡ just z
         → Is-just x
    J⇒IJ (just x) f _≡_.refl = DMRN.just _
    dij : (x : Strong)
        → (_ : P x)
        → apDec read P? x ≡ just _
    dij x p = begin
      apDec read P? x ≡⟨ _≡_.refl ⟩
      apDec.apDec' read x (P? x) ≡⟨ _≡_.refl ⟩
      _ ≡⟨ proj₂ D ▹ cong (apDec.apDec' read x) ⟩
      apDec.apDec' read x (yes $ proj₁ D) ∎
      where
      D = Relation.Nullary.Decidable.dec-yes (P? x) p
      open Relation.Binary.PropositionalEquality.≡-Reasoning

  nad = {!!}

module readℕ where
    private
      j : {m n : ℕ} → m ℕ.< n → Maybe $ Fin n
      j = just ∘ 𝔽.fromℕ<

    IsDigit : Char → Set
    toFin10 : Char → Maybe $ Fin 10
    IsDigit = Is-just ∘ toFin10
    toFin10 '0' = just 𝔽.zero
    toFin10 '1' = j $ from-yes $ 1 ℕ.<? 10
    toFin10 '2' = j $ from-yes $ 2 ℕ.<? 10
    toFin10 '3' = j $ from-yes $ 3 ℕ.<? 10
    toFin10 '4' = j $ from-yes $ 4 ℕ.<? 10
    toFin10 '5' = j $ from-yes $ 5 ℕ.<? 10
    toFin10 '6' = j $ from-yes $ 6 ℕ.<? 10
    toFin10 '7' = j $ from-yes $ 7 ℕ.<? 10
    toFin10 '8' = j $ from-yes $ 8 ℕ.<? 10
    toFin10 '9' = j $ from-yes $ 9 ℕ.<? 10
    toFin10 _ = nothing

    IsDigit? : Decidable IsDigit
    IsDigit? x with toFin10 x
    ... | just _ = yes $ DMRN.just _
    ... | nothing = no $ λ ()

    djm0 : Strong → Set
    djm0 = λ n → 𝕃All.All IsDigit n × 𝕃.length n ℕ.> 0

    read' : {x : Strong} → djm0 x → ℕ
    read' = 𝕃.sum ∘ 𝕃.map tenfa ∘ indice ∘ namste ∘ proj₁
      where
      tenfa = λ (b , e) → b ℕ.* 10 ℕ.^ e
      indice = λ x → 𝕃.zip x $ 𝕃.reverse $ 𝕃.upTo $ 𝕃.length x
      namste = 𝕃.map (𝔽.toℕ ∘ to-witness ∘ proj₂) ∘ 𝕃All.toList

module readList {a p : Level.Level} {A : Set a} ⦃ R : Read A ⦄ where
  Ps : Strong → (Strong → Set) → Strong → Set p
  Ps s P x =
      (Σ
        (Strong ×_ $ List $ Strong × ℕ × ℕ)
        (λ (s , xs) →
          (_×_
            (P s ×_ $ 𝕃All.All (Read.P R) $ 𝕃.map proj₁ xs)
            (_≡_
              x
              (let im = λ s f → 𝕃.intercalate s ∘ 𝕃.map f in
               ('[' ∷ []) 𝕃.++ im s f xs 𝕃.++ (']' ∷ []) 𝕃.++ s)))))
    where
    cbs = Function.flip 𝕃.replicate ' '
    f = λ (x , s₁ , s₂) → cbs s₁ 𝕃.++ x 𝕃.++ cbs s₂
  ≡∷[]? : Strong → Set
  ≡∷[]? x =
    (Σ
      (ℕ × ℕ)
      (λ (n₁ , n₂) →
        (_≡_
          x
          (𝕃.concat $
            𝕃.replicate n₁ ' ' ∷
            ('∷' ∷ []) ∷
            𝕃.replicate n₂ ' ' ∷
            ('[' ∷ ']' ∷ []) ∷
            []))))

  data P (x : Strong) : Set p
    where
    xaste : -- [1,2,3]
      (Σ
        (List Strong)
        (λ s →
          (_×_
            (𝕃All.All (Read.P R) s)
            (_≡_
              x
              (let S = 𝕃.intercalate (',' ∷ []) s in
               ('[' ∷ []) 𝕃.++ S 𝕃.++ (']' ∷ []))))))
      → P x
    xastes : -- [1,  2  ,    3 ]
      Ps (',' ∷ []) (_≡ 𝕃.[]) x → P x
    agasp : -- 1 ∷ 2 ∷ 3 ∷ []
      Ps (' ' ∷ '∷' ∷ ' ' ∷ []) ≡∷[]? x → P x
      
  read : Σ.∃ P → List A
  read (x , xaste (s , (r , d))) =
    𝕃.map (Read.read R _ ∘ proj₂) $ 𝕃All.toList r
  read (x , xastes (s , ((p , r) , d))) =
    𝕃.map (Read.read R _ ∘ proj₂) $ 𝕃All.toList r
  read (x , agasp (s , ((p , r) , d))) =
    𝕃.map (Read.read R _ ∘ proj₂) $ 𝕃All.toList r

instance
  readℕ : Read ℕ
  readℕ = record {
    read = λ x → readℕ.read' {x}
    }

  readMaybeℕ : ReadMaybe ℕ
  readMaybeℕ = record {
    rr = readℕ;
    P? = P?
    }
    where
    P? : Decidable readℕ.djm0
    P? x with 𝕃All.all? readℕ.IsDigit? x | 𝕃.length x ℕ.>? 0
    ... | yes p | yes l = yes $ p , l
    ... | no p | _ = no $ p ∘ proj₁
    ... | _ | no l = no $ l ∘ proj₂

    open Read readℕ

  readℤ : Read ℤ
  readℤ = record {
    P = λ s → 
      (_⊎_
        (readℕ.djm0 s)
        (_×_
          (𝕃.head s ≡ just '-')
          (readℕ.djm0 $ 𝕃.drop 1 s)));
    read = λ x → read {x}
    }
    where
    read : {x : Strong} → _ ⊎ _ → ℤ
    read (_⊎_.inj₁ z) = ℤ.+ Read.read readℕ _ z
    read (_⊎_.inj₂ (_ , m)) = ℤ.-_ $ ℤ.+ Read.read readℕ _ m

  read𝔽 : {n : ℕ} → Read $ Fin n
  read𝔽 = record {
    P = λ s → Σ.∃ $ (ℕ._< _) ∘ Read.read readℕ s;
    read = λ _ (_ , m) → 𝔽.fromℕ< m
    }

  readMaybe𝔽 : {n : ℕ} → ReadMaybe $ Fin n
  readMaybe𝔽 {n} = record {
    rr = read𝔽;
    P? = P?
    }
    where
    P? : Decidable _
    P? x with ReadMaybe.P? readMaybeℕ x
    ... | no j = no $ j ∘ proj₁
    ... | yes p with Read.read readℕ x p ℕ.<? n
    ... | yes p₁ = yes $ p , p₁
    ... | no j = no $ λ (z₁ , z₂) → subst (¬_ ∘ (ℕ._< n)) (d p z₁) j z₂
      where
      d : (p₁ p₂ : _)
        → Read.read readℕ x p₁ ≡ Read.read readℕ x p₂
      d = {!!}

  readChar : Read Char
  readChar = record {
    P = λ s → Σ Char $ λ c → s ≡ '\'' ∷ c ∷ '\'' ∷ [];
    read = λ _ → proj₁
    }

  readMaybeChar : ReadMaybe Char
  readMaybeChar = record {
    rr = readChar;
    P? = P?
    }
    where
    P? : (x : Strong) → Dec $ Read.P readChar x
    P? ('\'' ∷ c ∷ '\'' ∷ []) = yes $ c , _≡_.refl
    P? (x₁ ∷ z ∷ x₂ ∷ []) = {!!}
    P? [] = no $ λ ()
    P? (x ∷ []) = no $ λ ()
    P? (x₁ ∷ x₂ ∷ []) = no $ λ ()
    P? (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ xs) = no $ λ ()

  readℚ : Read {p = {!!}} ℚ
  readℚ = record {
    P = λ s →
      (Σ
        (Σ
          (Strong × Strong)
          (λ (s₁ , s₂) →
            Read.P readℤ s₁ × Read.P readℕ s₂))
        (λ ((s₁ , s₂) , (p₁ , p₂)) →
          let n₁ = Read.read readℤ s₁ p₁ in
          let n₂ = Read.read readℕ s₂ p₂ in
          (_×_
            (Coprime ℤ.∣ n₁ ∣ (ℕ.suc n₂))
            (s ≡ s₁ 𝕃.++ 𝕃.[ '/' ] 𝕃.++ s₂))));
    read = (λ s (((s₁ , s₂) , p₁ , p₂) , (cpr) , d) →
      ℚ.mkℚ (Read.read readℤ s₁ p₁) (Read.read readℕ s₂ p₂) cpr)
    }

  readMaybeℚ : ReadMaybe ℚ
  readMaybeℚ = record {
    rr = readℚ;
    P? = f
    }
    where
    f : (x : Strong) → Dec $ Read.P readℚ x
    f x with 𝕃.linesBy (_≟ '/') x
    ... | zp ∷ np ∷ [] = {!!}
    ... | x ∷ [] = {!!}
    ... | [] = {!!}
    ... | (x₁ ∷ x₂ ∷ x₃ ∷ xs) = {!!}

  readList : ∀ {a p} → {A : Set a}
           → ⦃ Read {p = p} A ⦄
           → Read $ List A
  readList {p = p} {A} ⦃ R ⦄ = record {
    P = readList.P;
    read = Σ.curry readList.read
    }

  readMaybeList : ∀ {a p} → {A : Set a}
                → ⦃ ReadMaybe {p = p} A ⦄
                → ReadMaybe {p = p} $ List A
  readMaybeList = {!!}
\end{code}

\begin{code}
record Show {a} (A : Set a) : Set a
  where
  field
    show : A → Strong

instance
  {-# TERMINATING #-}
  showNat : Show ℕ
  showNat = record {
    show = show
    }
    where
    show : ℕ → Strong
    show = show' ˢ (ℕ._<? 10)
      where
      show' : (n : ℕ) → Dec $ n ℕ.< 10 → Strong
      show' _ (yes p) = 𝕃.[_] $ s $ 𝔽.fromℕ< p
        where
        s : Fin 10 → Char
        s 𝔽.zero = '0'
        s 𝔽.1F = '1'
        s 𝔽.2F = '2'
        s 𝔽.3F = '3'
        s 𝔽.4F = '4'
        s 𝔽.5F = '5'
        s 𝔽.6F = '6'
        s 𝔽.7F = '7'
        s 𝔽.8F = '8'
        s 𝔽.9F = '9'
      show' n (no _) = show' (n ℕ.div 10) (_ ℕ.<? 10) 𝕃.++ romoi
        where
        romoi = show' (n ℕ.% 10) (yes $ ℕ.m%n<n n 9)

  showInt : Show ℤ
  showInt = record {
    show = λ z → s z 𝕃.++ Show.show showNat ℤ.∣ z ∣
    }
    where
    s : ℤ → Strong
    s z = if (isYes $ z ℤ.<? ℤ.0ℤ) ('-' ∷ []) []

  showList : ∀ {a} → {A : Set a}
           → ⦃ Show A ⦄
           → Show $ List A
  showList {a} {A} ⦃ S ⦄ = record {
    show = λ x → 𝕃.[ '[' ] 𝕃.++ s x 𝕃.++ 𝕃.[ ']' ]
    }
    where
    s = 𝕃.intercalate 𝕃.[ ',' ] ∘ 𝕃.map (Show.show S)
\end{code}

\begin{code}
readMaybe : ∀ {a p} → {A : Set a}
          → ⦃ ReadMaybe {p = p} A ⦄
          → Strong
          → Maybe A
readMaybe ⦃ Q ⦄ = ReadMaybe.readMaybe Q

show : ∀ {a} → {A : Set a} → ⦃ Show A ⦄ → A → Strong
show ⦃ Q ⦄ = Show.show Q
\end{code}
\end{document}
