\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{xcolor}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb{S}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb{Q}}}}
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb{R}}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb{Z}}}}
\newunicodechar{ℂ}{\ensuremath{\mathnormal{\mathbb{C}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{⁻}{\ensuremath{\mathnormal{^-}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathnormal{\mathrm{?\!?}}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal{\ell}}}
\newunicodechar{σ}{\ensuremath{\mathnormal{\sigma}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\mathsf{m}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\mathsf{s}}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{⊥}{\ensuremath{\mathnormal{\bot}}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}
\newunicodechar{ₙ}{\ensuremath{\mathnormal{_n}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{′}{\ensuremath{\mathnormal{'}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≗}{\ensuremath{\mathnormal{\circeq}}}
\newunicodechar{⇒}{\ensuremath{\mathnormal{\Rightarrow}}}
\newunicodechar{⇐}{\ensuremath{\mathnormal{\Leftarrow}}}
\newunicodechar{≈}{\ensuremath{\mathnormal{\approx}}}
\newunicodechar{≉}{\ensuremath{\mathnormal{\napprox}}}
\newunicodechar{⌊}{\ensuremath{\mathnormal{\lfloor}}}
\newunicodechar{⊓}{\ensuremath{\mathnormal{\sqcap}}}
\newunicodechar{⊔}{\ensuremath{\mathnormal{\sqcup}}}
\newunicodechar{⍨}{\raisebox{-0.25ex}{$\ddot\sim$}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{la'o zoi.\ \texttt{Truthbrary.Data.Mrena'u}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
\noindent
ni'o bau la .lojban.\ joi la'oi .Agda.\ la .varik.\ cu ciksi ko'a goi lo mrena'u se ctaipe ge'u je lo jai filri'a be tu'a ko'a
\end{abstract}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Truthbrary.Data.Mrena'u where

open import Level
  using (
  )
open import Algebra
  using (
    LeftIdentity;
    Associative;
    Commutative;
    IsRing;
    Zero
  )
open import Data.Fin
  as 𝔽
  using (
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  as _⊎_
  using (
    _⊎_
  )
open import Function
  using (
    const;
    _∘_;
    _$_
  )
  renaming (
    flip to _⍨
  )
open import Data.Bool
  as 𝔹
  using (
    if_then_else_
  )
open import Data.Sign
  using (
    Sign
  )
open import Data.Digit
  using (
    Digit
  )
open import Data.Integer
  as ℤ
  using (
    ℤ
  )
open import Data.Product
  using (
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃
  )
open import Data.Rational
  as ℚ
  using (
    ℚ
  )
open import Relation.Binary
  using (
    Asymmetric;
    Reflexive
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Data.Fin.Patterns
  using (
    9F
  )
open import Relation.Nullary.Negation
  using (
  )
  renaming (
    contradiction to _⇒⇐_
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    subst;
    _≗_;
    _≡_;
    sym
  )
\end{code}

\section{la'oi .\F ℝ.}
ni'o ro da zo'u da mrena'u jo cu ctaipe la'oi .\F ℝ.  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B s \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore{}}\B a \B b\Sym)\ .zoi.\ poi ke'a ctaipe la'oi .\F ℝ.\ cu pilji lo sumji be la'oi .\B a.\ bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.\ zo'e poi ga jonai ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.+}\ .zoi.\ gi ke'a du li pa gi ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.-}\ .zoi.\ gi ke'a du li ni'u pa  .i ga jo la'oi .\F ℝ.\ se ctaipe ko'a goi la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \AgdaUnderscore{} \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore} \AgdaUnderscore\ \B f\Sym)\ .zoi.\ gi la'o zoi.\ \B f \B n\ .zoi.\ meirmoi la'oi .\B n.\ fo lo me'oi .digit.\ be lo cmalu pagbu be lo mu'oi glibau.\ decimal expansion .glibau.\ be ko'a

.i la .varik.\ cu pacna lo nu frili cumki fa lo nu xagzengau pe'a le velcki

\begin{code}
ℝ : Set
ℝ = Sign × ℕ × (ℕ → Digit 10)
\end{code}

\subsection{tu'a li ni'u no}
ni'o la'oi .\F ℝ.\ jai .indika le du'u li no na du li ni'u no  .i la .varik.\ na mutce le ka ce'u tolnei la'e di'u  .i krinu la'e di'u fa le su'u la .varik.\ cu nelci le su'u sampu  .i ku'i cumki fa lo nu la .varik.\ cu binxo

\section{la'o zoi.\ \F{\AgdaUnderscore{}≈\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B r \OpF ≈ \B s\ .zoi.\ gi la'oi .\B r.\ namcu du la'oi .\B s.

\begin{code}
_≈_ : ℝ → ℝ → Set
_≈_ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ zmadu la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≥\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≥ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavmau la'oi .\B b.

\begin{code}
_≥_ : ℝ → ℝ → Set
_≥_ = λ r s → (r ≈ s) ⊎ (r > s)
\end{code}

\section{la'o zoi.\ \F{⌊'}\ .zoi.}
ni'o du la'oi .\B r.\ fa lo sumji be la'o zoi.\ \F{⌊'} \B r\ .zoi.\ be lo co'e be la'o zoi.\ \AgdaField{proj₂} \OpF \$ \AgdaField{proj₂} \B r\ .zoi.

\begin{code}
⌊' : ℝ → ℤ
⌊' (Sign.+ , n , _) = ℤ.+_ n
⌊' (Sign.- , n , _) = ℤ.-_ $ ℤ.+_ n
\end{code}

\section{la'o zoi.\ \F{⌊'⁻¹}\ .zoi.}
ni'o la'o zoi.\ \F{⌊'⁻¹} \B r\ .zoi.\ mu'oi glibau.\ decimal expansion .glibau.\ co'e la'oi .\B r.  .i la .varik.\ cu stidi lo nu lo na jimpe cu tcidu le velcki be la'o zoi.\ \F{⌊'⁻¹}\ .zoi.\ be'o je le velcki be la'oi .\F ℝ.

\begin{code}
⌊'⁻¹ : ℝ → ℕ → Digit 10
⌊'⁻¹ = proj₂ ∘ proj₂
\end{code}

\section{la'o zoi.\ \F{⌊'⁻¹ℝ}\ .zoi.}
ni'o la'o zoi.\ \F{⌊'⁻¹ℝ} \B r\ .zoi.\ namcu du la'o zoi.\ \F{⌊'⁻¹} \B r\ .zoi.

\begin{code}
⌊'⁻¹ℝ : ℝ → ℝ
⌊'⁻¹ℝ (s , _ , r) = s , 0 , r
\end{code}

\section{la'oi .\F{sign}.}
ni'o ro da poi ke'a ctaipe la'oi .\F ℝ.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du li no gi li no du ko'a goi lo me'oi .\F{sign}.\ be da gi
	\item ga jonai ga je da mleca li no gi ko'a du li ni'u pa gi
	\item ga je da zmadu li no gi ko'a du li pa
\end{itemize}

\begin{code}
sign : ℝ → ℤ
sign = {!!}
\end{code}

\section{la'o zoi.\ \F{fromℕ} .zoi.}
ni'o la'o zoi.\ \F{fromℕ} \B n\ .zoi.\ namcu du la'oi .\B n.

\begin{code}
fromℕ : ℕ → ℝ
fromℕ n = Sign.+ , n , const 𝔽.zero
\end{code}

\section{la'o zoi.\ \F{fromℤ}\ .zoi.}
ni'o la'o zoi.\ \F{fromℤ} \B z\ .zoi.\ namcu dunli la'oi .\B z.

\begin{code}
fromℤ : ℤ → ℝ
fromℤ (ℤ.pos n) = Sign.+ , n , const 𝔽.zero
fromℤ (ℤ.negsuc n) = Sign.- , ℕ.suc n , const 𝔽.zero
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}+\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF + \B b\ .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_+_ : ℝ → ℝ → ℝ
_+_ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}-\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF - \B b\ .zoi.\ vujnu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_-_ : ℝ → ℝ → ℝ
_-_ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}*\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF * \B b\ .zoi.\ pilji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_*_ : ℝ → ℝ → ℝ
_*_ = {!!}
\end{code}

\section{la \F{frinu}}
ni'o la'o zoi.\ \F{frinu} \B a \B b \AgdaUnderscore{}\ .zoi.\ frinu la'oi .\B a.\ la'oi .\B b.

\begin{code}
frinu : (_ d : ℝ) → ¬_ $ d ≈ fromℕ 0 → ℝ
frinu = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}\textasciicircum{}\AgdaUnderscore}\ .zoi.}
ni'o tenfa la'oi .\B a.\ la'oi .\B b.\ fa la'o zoi.\ \B a \OpF \textasciicircum{} \B b\ .zoi.

\begin{code}
_^_ : ℝ → ℝ → ℝ
_^_ = {!!}
\end{code}

\section{la'o zoi.\ \F{fromℚ}\ .zoi.}
ni'o la'o zoi.\ \F{fromℚ} \B k\ .zoi.\ namcu dunli la'oi .\B k.

\begin{code}
module FromℚI where
  fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
  fromℕ[s]≉0 = {!!}

fromℚ : ℚ → ℝ
fromℚ (ℚ.mkℚ a b N) = frinu (fromℤ a) 1+b $ fromℕ[s]≉0 b
  where
  open FromℚI
  1+b = fromℕ $ ℕ.suc b
\end{code}

\section{la'oi .\F{Rational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Rational} \B r\ .zoi.\ gi la'oi .\B r.\ me'oi .rational.  .i cadga fa lo nu li'armi  .i le velcki zo'u ro da poi ke'a co'e zo'u da me'oi .irrational.\ jo cu du lo su'o frinu

\begin{code}
Rational : ℝ → Set
Rational r = ∃ $ _≈_ r ∘ fromℚ
\end{code}

\section{la'oi .\F{Irrational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Irrational} \B r\ .zoi.\ gi la'oi .\B r.\ me'oi .irrational.  .i cadga fa lo nu li'armi  .i le velcki zo'u ro da poi ke'a co'e zo'u da me'oi .irrational.\ jo cu du lo no frinu

\begin{code}
Irrational : ℝ → Set
Irrational = ¬_ ∘ Rational
\end{code}

\section{la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ .zoi.}
ni'o cu'alni la'oi .\B r.\ fa la'o zoi.\ \F{∣\AgdaUnderscore{}∣} \B r\ .zoi.

\begin{code}
∣_∣ : ℝ → ℝ
∣_∣ = _,_ Sign.+ ∘ proj₂
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}⊓\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B r \OpF ⊓ \B s\ .zoi.\ nacmecrai la'oi .\B r.\ ce la'oi .\B s.

\begin{code}
module _⊓_I where
  f : ∀ {a} → {A : Set a} → A → A → 𝔹.Bool → A
  f r s n = if_then_else_ n s r

  _>ᵇ_ : ℝ → ℝ → 𝔹.Bool
  _>ᵇ_ = {!!}

_⊓_ : ℝ → ℝ → ℝ
_⊓_ r s = f r s $ _>ᵇ_ r s
  where
  open _⊓_I
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}⊔\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B r \OpF ⊔ \B s\ .zoi.\ nacyzmarai la'oi .\B r.\ ce la'oi .\B s.

\begin{code}
_⊔_ : ℝ → ℝ → ℝ
_⊔_ r s = _⊓_I.f r s $ 𝔹.not $ _⊓_I._>ᵇ_ r s
\end{code}

\section{le ctaipe be le su'u mapti}

\begin{code}
module Veritas where
\end{code}

\newcommand\lcblm[1]{le ctaipe be le su'u mapti fa la'o zoi.\ #1\ .zoi.}

\subsection{\lcblm{\F{\AgdaUnderscore{}≈\AgdaUnderscore}}}

\begin{code}
  module _≈_ where
    r≈r : (r : ℝ) → r ≈ r
    r≈r = {!!}

    ≡∧≗⇒≈ : (r s : ℝ)
          → ⌊' r ≡ ⌊' s
          → ⌊'⁻¹ r ≗ ⌊'⁻¹ s
          → r ≈ s
    ≡∧≗⇒≈ = {!!}

    ≡⇒≈ : (r s : ℝ) → r ≡ s → r ≈ s
    ≡⇒≈ = {!!}

    ≈⇒≈⍨ : (r s : ℝ) → r ≈ s → s ≈ r
    ≈⇒≈⍨ = {!!}

    id≡[≈⇒≈⍨]² : (r s : ℝ)
               → (d : r ≈ s)
               → d ≡_ $ ≈⇒≈⍨ s r $ ≈⇒≈⍨ r s d
    id≡[≈⇒≈⍨]² = {!!}

    ≈∧≈⇒≈ : Relation.Binary.Transitive _≈_
    ≈∧≈⇒≈ = {!!}

    n,9+≈n+1 : (s : Sign)
             → (n : ℕ)
             → (_≈_
                 (s , n , const 9F)
                 (s , (ℕ.suc n) , const 𝔽.zero))
    n,9+≈n+1 = {!!}

    >⇒≉ : (r s : ℝ)
        → {k : ℚ}
        → ¬_ $ fromℚ k ≈ fromℕ 0
        → ∣ r - s ∣ > fromℚ k
        → ¬_ $ r ≈ s
    >⇒≉ = {!!}

    ≈⇒fn≡gn : (r s : ℝ)
            → ⌊' r ≡ ⌊' s
            → r ≈ s
            → ⌊'⁻¹ r ≗ ⌊'⁻¹ s
    ≈⇒fn≡gn = {!!}

    setoid : Relation.Binary.Setoid _ _
    setoid = record {
      _≈_ = _≈_;
      isEquivalence = record {
        refl = λ {r} → r≈r r;
        sym = {!!};
        trans = λ {i} {j} {k} → ≈∧≈⇒≈ {i} {j} {k}}}
\end{code}

\subsection{\lcblm{\F{fromℕ}}}

\begin{code}
  module Fromℕ where
    pav : (n : ℕ) → ℤ.+_ n ≡ ⌊' (fromℕ n)
    pav _ = _≡_.refl

    rel : (m n : ℕ) → 𝔽.zero ≡ ⌊'⁻¹ (fromℕ m) n
    rel _ _ = _≡_.refl

    fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
    fromℕ[s]≉0 = FromℚI.fromℕ[s]≉0

    fromℕ-Rational : (n : ℕ) → Rational $ fromℕ n
    fromℕ-Rational n = ℚ.mkℚ (ℤ.+_ n) 1 {!!} , {!!}

  module _+_ where
    +≈+⍨ : Commutative _≈_ _+_
    +≈+⍨ = {!!}

    +-ass : Associative _≈_ _+_
    +-ass = {!!}

    id≡+0 : Algebra.Identity _≡_ (fromℕ 0) _+_
    id≡+0 = {!!} , {!!}

    dratadratas : (r s : ℝ)
                → ¬_ $ r ≈ s
                → let N = ¬_ ∘ _≈_ (r + s) in
                  N r × N s
    dratadratas = {!!}

    r≡r₁+r₂ : (r : ℝ) → r ≡_ $ fromℤ (⌊' r) + ⌊'⁻¹ℝ r
    r≡r₁+r₂ = {!!}

    r≡r₂+r₁ : (r : ℝ) → r ≡_ $ ⌊'⁻¹ℝ r + fromℤ (⌊' r)
    r≡r₂+r₁ = {!!}

    rn+sn≡[r+s]n : (z₁ z₂ : ℤ)
                 → fromℤ (z₁ ℤ.+ z₂) ≡ fromℤ z₁ + fromℤ z₂
    rn+sn≡[r+s]n = {!!}

    r≡f+n : (s : Sign)
          → (n : ℕ)
          → (f : ℕ → Digit 10)
          → (_≡_
              (s , n , f)
              (_+_
                (s , 0 , f)
                (s , n , const 𝔽.zero)))
    r≡f+n = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}-\AgdaUnderscore}}}

\begin{code}
  module _-_ where
    0≈r-r : (r : ℝ) → fromℕ 0 ≈_ $ r - r
    0≈r-r = {!!}

    r≈-r⇒r≈0 : (r : ℝ)
             → r ≈_ $ fromℕ 0 - r
             → r ≈ fromℕ 0
    r≈-r⇒r≈0 = {!!}

    0≡r-0 : Algebra.RightZero _≡_ (fromℕ 0) _-_
    0≡r-0 = {!!}

    r-s-t≈r-[s+t] : (r s t : ℝ) → ((r - s) - t) ≈ (r - (s + t))
    r-s-t≈r-[s+t] = {!!}

    0-[+r]≈-r : (n : ℕ)
              → (f : _)
              → ((_≈_ ⍨)
                  (Sign.- , n , f)
                  (fromℕ 0 -_ $ Sign.+ , n , f))
    0-[+r]≈-r = {!!}

    r≈[r-s]+s : (r s : ℝ) → r ≈_ $ (r - s) + s
    r≈[r-s]+s = {!!}

    r≈0-[0-r] : (r : ℝ) → r ≈_ $ fromℕ 0 -_ $ fromℕ 0 - r
    r≈0-[0-r] = {!!}

    r>r-s : (r s : ℝ) → s > fromℕ 0 → r >_ $ r - s
    r>r-s = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}*\AgdaUnderscore}}}

\begin{code}
  module _*_ where
    r≈1*r : Algebra.Identity _≈_ (fromℕ 1) _*_
    r≈1*r = {!!}

    0≈0*r : Zero _≈_ (fromℕ 0) _*_
    0≈0*r = {!!}

    *≈*⍨ : Commutative _≈_ _*_
    *≈*⍨ = {!!}

    *-ass : Associative _≈_ _*_
    *-ass = {!!}

    r*n≈? : (r : ℝ)
          → (n : ℕ)
          → (_≈_
              (r * fromℕ n)
              (_+_
                (proj₁ r , 0 , {!!})
                (fromℤ $ ℤ._+_
                  (⌊' r ℤ.* ℤ.+_ 10)
                  {!!})))
    r*n≈? = {!!}

    r*10≈_ : (r : ℝ)
           → (_≈_
               (r * fromℕ 10)
               (_+_
                 (proj₁ r , 0 , ⌊'⁻¹ r ∘ ℕ.suc)
                 (fromℤ $ ℤ._+_
                   (⌊' r ℤ.* ℤ.+_ 10)
                   ({!!} ℤ.*_ $ ℤ.+_ $ 𝔽.toℕ $ ⌊'⁻¹ r 0))))
    r*10≈_ = {!!}

    r*s>r : (r s : ℝ)
          → r > fromℕ 0
          → s > fromℕ 1
          → (r * s) > r
    r*s>r = {!!}

    r>r*s : (r s : ℝ)
          → r > fromℕ 0
          → fromℕ 1 > s
          → r >_ $ r * s
    r>r*s = {!!}
\end{code}

\subsection{\lcblm{\F{frinu}}}

\begin{code}
  module Frinu where
    module I where
      r>1⇒r≉0 : (r : ℝ) → r > fromℕ 1 → ¬_ $ r ≈ fromℕ 0
      r>1⇒r≉0 = {!!}

    sez≡1 : (r : ℝ) → (N : _) → frinu r r N ≡ fromℕ 1
    sez≡1 = {!!}

    r≡r/1 : (r : ℝ) → r ≡ frinu r (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0)
    r≡r/1 = {!!}

    0≡0/r : (r : ℝ) → (N : _) → fromℕ 0 ≡ frinu (fromℕ 0) r N
    0≡0/r = {!!}

    r/s<r : (r s : ℝ) → (z : s > fromℕ 1) → r > frinu r s (I.r>1⇒r≉0 s z)
    r/s<r = {!!}

    r<r/s : (r s : ℝ) → (N : _) → fromℕ 1 > s → r > frinu r s N
    r<r/s = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}\textasciicircum\AgdaUnderscore}}}

\begin{code}
  module _^_ where
    id≡_^1 : Algebra.RightIdentity _≡_ (fromℕ 1) _^_
    id≡_^1 = {!!}

    1≡1^r : (r : ℝ) → fromℕ 1 ≡_ $ fromℕ 1 ^ r
    1≡1^r = {!!}

    1≡r^0 : (r : ℝ) → fromℕ 1 ≡_ $ r ^ fromℕ 0
    1≡r^0 = {!!}

    0≡0^r : (r : ℝ)
          → ¬_ $ r ≈ fromℕ 0
          → fromℕ 0 ≡_ $ fromℕ 0 ^ r
    0≡0^r = {!!}

    0^0≡1 : fromℕ 0 ^ fromℕ 0 ≡ fromℕ 1
    0^0≡1 = sym $ 1≡r^0 $ fromℕ 0

    [r^s]^t≈r^[s*t] : (r s t : ℝ) → ((r ^ s) ^ t) ≈ (r ^ (s * t))
    [r^s]^t≈r^[s*t] = {!!}

    r≈[r^s]^[1/s] : (r s : ℝ)
                  → (N : _)
                  → (_≈_
                      r
                      (_^_
                        (r ^ s)
                        (frinu (fromℕ 1) s N)))
    r≈[r^s]^[1/s] = {!!}
\end{code}

\subsection{\lcblm{\F{⌊'}}}

\begin{code}
  module ⌊' where
    fromℤ∘⌊' : (r : ℝ)
            → ⌊'⁻¹ r ≗ const 𝔽.zero
            → r ≡ fromℤ (⌊' r)
    fromℤ∘⌊' = {!!}

    ⌊'∘fromℤ : (z : ℤ) → z ≡_ $ ⌊' $ fromℤ z
    ⌊'∘fromℤ = {!!}

    ∃f≡ : (r : ℝ) → ∃ $ λ f → r ≡ f + fromℤ (⌊' r)
    ∃f≡ r = ⌊'⁻¹ℝ r , _+_.r≡r₂+r₁ r
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}>\AgdaUnderscore}}}

\begin{code}
  module _>_ where
    ¬sez : (r : ℝ) → ¬_ $ r > r
    ¬sez = {!!}

    +-zmad : (r s : ℝ) → s > fromℕ 0 → (r + s) > r
    +-zmad = {!!}

    >⇒¬< : Asymmetric _>_
    >⇒¬< = {!!}

    ∃[>∧>⍨] : (r s : ℝ) → r > s → ∃ $ λ t → (r > t) × (t > s)
    ∃[>∧>⍨] r s z = frinu (r + s) (fromℕ 2) N , {!!} , {!!}
      where
      N = Fromℕ.fromℕ[s]≉0 1

    >∧>⇒> : (r s t : ℝ) → r > s → s > t → r > t
    >∧>⇒> = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}≥\AgdaUnderscore}}}

\begin{code}
  module _≥_ where
    sez : Reflexive _≥_
    sez {r} = _⊎_.inj₁ $ _≈_.≡⇒≈ r r _≡_.refl

    ≈⇒≥ : {r s : ℝ} → r ≈ s → r ≥ s
    ≈⇒≥ = _⊎_.inj₁

    >⇒≥ : {r s : ℝ} → r > s → r ≥ s
    >⇒≥ = _⊎_.inj₂

    ≥∧≉⇒> : {r s : ℝ} → r ≥ s → ¬_ $ r ≈ s → r > s
    ≥∧≉⇒> (_⊎_.inj₁ d) N = d ⇒⇐ N
    ≥∧≉⇒> (_⊎_.inj₂ z) N = z

    ≥∧¬>⇒≈ : {r s : ℝ} → r ≥ s → ¬_ $ r > s → r ≈ s
    ≥∧¬>⇒≈ (_⊎_.inj₁ d) N = d
    ≥∧¬>⇒≈ (_⊎_.inj₂ z) N = z ⇒⇐ N
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}⊓\AgdaUnderscore}}}

\begin{code}
  module _⊓_ where
    module I where
      open _⊓_I
        using (
          _>ᵇ_;
          f
        )

      ≥⇒⊤ : (r s : ℝ) → r ≥ s → 𝔹.true ≡ _>ᵇ_ r s
      ≥⇒⊤ = {!!}

      ⊤⇒≥ : (r s : ℝ) → 𝔹.true ≡ _>ᵇ_ r s → r ≥ s
      ⊤⇒≥ = {!!}

      <⇒⊥ : (r s : ℝ) → s > r → 𝔹.false ≡ _>ᵇ_ r s
      <⇒⊥ = {!!}

      ⊥⇒≤ : (r s : ℝ) → 𝔹.false ≡ _>ᵇ_ r s → s ≥ r
      ⊥⇒≤ = {!!}

      ⊥⇒1 : ∀ {a} → {A : Set a}
          → {x : A}
          → (z : A)
          → x ≡ f x z 𝔹.false
      ⊥⇒1 _ = _≡_.refl

      ⊤⇒2 : ∀ {a} → {A : Set a}
          → (x : A)
          → {z : A}
          → z ≡ f x z 𝔹.true
      ⊤⇒2 _ = _≡_.refl

    <⇒1 : (r s : ℝ) → s > r → r ≡ r ⊓ s
    <⇒1 r s z = subst (_≡_ r ∘ _⊓_I.f r s) (I.<⇒⊥ r s z) (I.⊥⇒1 s)

    ≥⇒2 : (r s : ℝ) → r ≥ s → s ≡ r ⊓ s
    ≥⇒2 r s z = subst (_≡_ s ∘ _⊓_I.f r s) (I.≥⇒⊤ r s z) (I.⊤⇒2 r)

    ≈⇒1 : (r s : ℝ) → r ≈ s → r ≈ (r ⊓ s)
    ≈⇒1 = {!!}

    ≈⇒2 : (r s : ℝ) → r ≈ s → s ≈ (r ⊓ s)
    ≈⇒2 = {!!}

    ⊓≈⊓⍨ : Commutative _≈_ _⊓_
    ⊓≈⊓⍨ = {!!}

    ⊓-ass : Associative _≈_ _⊓_
    ⊓-ass = {!!}
\end{code}

\section{le ctaipe be le su'u sumji joi co'e me'oi .group.}

\begin{code}
+--group : Algebra.IsGroup _≈_ _+_ (fromℕ 0) (fromℕ 0 -_)
+--group = record {
  isMonoid = {!!};
  inverse = {!!};
  ⁻¹-cong = {!!}}
\end{code}

\section{le ctaipe be le su'u sumji mu'oi glibau.\ abelian group .glibau.}

\begin{code}
ga+ : Algebra.IsAbelianGroup _≈_ _+_ (fromℕ 0) (fromℕ 0 -_)
ga+ = record {
  isGroup = +--group;
  comm = Veritas._+_.+≈+⍨}
\end{code}

\section{le ctaipe be le su'u me'oi .ring.}

\begin{code}
isRing : IsRing _≈_ _+_ _*_ (fromℕ 0 -_) (fromℕ 0) (fromℕ 1)
isRing = record {
  +-isAbelianGroup = ga+;
  *-isMonoid = {!!};
  distrib = {!!};
  zero = Veritas._*_.0≈0*r}
\end{code}
\end{document}
