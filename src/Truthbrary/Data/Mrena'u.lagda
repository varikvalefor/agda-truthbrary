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
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{⟪}{\ensuremath{\mathnormal{\langle\hspace{-0.2em}\langle}}}
\newunicodechar{⟫}{\ensuremath{\mathnormal{\rangle\hspace{-0.2em}\rangle}}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{¯}{\ensuremath{\mathnormal{^-}}}
\newunicodechar{◃}{\ensuremath{\mathnormal\triangleleft}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{𝕗}{\ensuremath{\mathnormal{\mathbb{f}}}}
\newunicodechar{ℙ}{\ensuremath{\mathnormal{\mathbb{P}}}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb{F}}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb{S}}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb{M}}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb{L}}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb{Q}}}}
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb{R}}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb{Z}}}}
\newunicodechar{𝔻}{\ensuremath{\mathnormal{\mathbb{D}}}}
\newunicodechar{ℂ}{\ensuremath{\mathnormal{\mathbb{C}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∙}{\ensuremath{\mathnormal\bullet}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˢ}{\ensuremath{\mathnormal{^\AgdaFontStyle{s}}}}
\newunicodechar{⁻}{\ensuremath{\mathnormal{^-}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{≯}{\ensuremath{\mathnormal{\ngtr}}}
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
\newcommand\Mod\AgdaModule
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
{-# OPTIONS
  --safe
  --cubical-compatible
#-}

module Truthbrary.Data.Mrena'u where

open import Algebra
  using (
    LeftIdentity;
    Associative;
    Commutative;
    Identity;
    IsRing;
    Zero;
    Op₂
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
  as _⊎_
  using (
    _-⊎-_;
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    const;
    _∘₂_;
    _on_;
    _∋_;
    _∘′_;
    _ˢ_;
    _∘_;
    _$_;
    id
  )
  renaming (
    _|>_ to _▹_;
    flip to _⍨
  )
open import Data.Bool
  as 𝔹
  using (
    if_then_else_;
    false;
    Bool;
    true;
    not
  )
open import Data.List
  as 𝕃
  using (
    List
  )
open import Data.Sign
  as Sign
  using (
    Sign
  )
open import Data.Digit
  using (
    Digit
  )
open import Data.Empty
  using (
    ⊥
  )
open import Data.These
  as These
  using (
  )
  renaming (
    These to _∨_
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
    _-×-_;
    _,′_;
    _×_;
    _,_;
    ∃
  )
open import Data.Rational
  as ℚ
  using (
    ℚ
  )
open import Relation.Unary
  using (
    _⊆′_;
    Pred;
    _⊆_
  )
open import Data.Nat.DivMod
  as ℕ
  using (
  )
open import Relation.Binary
  using (
    Irreflexive;
    Asymmetric;
    Transitive;
    Reflexive;
    Setoid;
    _⇒_
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Data.Fin.Patterns
  using (
    9F
  )
open import Data.Integer.DivMod
  as ℤ
  using (
  )
open import Data.Nat.Coprimality
  as Coprime
  using (
    1-coprimeTo
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
    refl;
    sym
  )

import Data.Rational.Literals
  as ℚ
  using (
    fromℤ
  )
\end{code}

\section{la'oi .\F ℝ.}
ni'o ro da zo'u da mrena'u jo cu ctaipe la'oi .\F ℝ.  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B s \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore{}}\B a \B b\Sym)\ .zoi.\ poi ke'a ctaipe la'oi .\F ℝ.\ cu pilji lo sumji be la'oi .\B a.\ bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.\ zo'e poi ga jonai ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.+}\ .zoi.\ gi ke'a du li pa gi ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.-}\ .zoi.\ gi ke'a du li ni'u pa  .i ga jo la'oi .\F ℝ.\ se ctaipe ko'a goi la'o zoi.\ \AgdaUnderscore{} \AgdaOperator{\IC,} \Sym(\AgdaUnderscore{} \AgdaOperator{\IC,} \B f\Sym)\ .zoi.\ gi la'o zoi.\ \B f \B n\ .zoi.\ meirmoi la'oi .\B n.\ fo lo'i me'oi .digit.\ be lo cmalu pagbu be lo mu'oi glibau.\ decimal expansion .glibau.\ be ko'a

.i la .varik.\ cu pacna lo nu frili cumki fa lo nu xagzengau pe'a le lojbo je velcki

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
_≈_ = ⊎/ $ _≡_ 𝕃.∷ {!!}
  where
  ⊎/ : ∀ {a} → {A : Set a} → let C = A → A → Set in List C → C
  ⊎/ = 𝕃.foldr _-⊎-_ $ λ _ _ → ⊥
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ dubmau la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}<\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{<} \B b\ .zoi.\ gi la'oi .\B a.\ dubme'a la'oi .\B b.

\begin{code}
_<_ : ℝ → ℝ → Set
_<_ = _>_ ⍨
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≥\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≥ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavmau la'oi .\B b.

\begin{code}
_≥_ : ℝ → ℝ → Set
_≥_ = _≈_ -⊎- _>_
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≤\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≤ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavme'a la'oi .\B b.

\begin{code}
_≤_ : ℝ → ℝ → Set
_≤_ = _≥_ ⍨
\end{code}

\section{la'o zoi.\ \F{⌊'}\ .zoi.}
ni'o du la'oi .\B r.\ fa lo sumji be la'o zoi.\ \F{⌊'} \B r\ .zoi.\ bei lo pilji be lo me'oi .sign.\ namcu be la'oi .\B r.\ be'o bei lo namcu poi ke'a dubjavmau li re je cu dubme'a li pa\ldots be'o be'o noi ke'a sumji la'o zoi.\ \F{⌊'} \B r\ .zoi.\ lo co'e be la'o zoi.\ \AgdaField{proj₂} \OpF \$ \AgdaField{proj₂} \B r\ .zoi.

\begin{code}
⌊' : ℝ → ℤ
⌊' (Sign.+ , n , _) = ℤ.+ n
⌊' (Sign.- , n , _) = ℤ.- (ℤ.+ n)
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
ni'o ro da poi ke'a ctaipe la'oi .\F ℝ.\ zo'u ga jonai ga je da zmadu li no gi du la'o zoi.\ \IC{Sign.+}\ .zoi.\ fa ko'a goi lo me'oi .\F{sign}.\ be da gi ko'a du la'o zoi.\ \IC{Sign.-}\ .zoi.  .i ku'i .indika fa zo'e po la'o zoi.\ \Mod{Veritas.SignV}\ .zoi.

\begin{code}
sign : ℝ → Sign
sign = proj₁
\end{code}

\section{la'oi .\F{signℤ}.}
ni'o ro da poi ke'a ctaipe la'oi .\F ℝ.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du li no gi li no du ko'a goi lo me'oi .\F{signℤ}.\ be da gi
	\item ga jonai ga je da mleca li no gi ko'a du li ni'u pa gi
	\item ga je da zmadu li no gi ko'a du li pa
\end{itemize}

\begin{code}
signℤ : ℝ → ℤ
signℤ = {!!}
\end{code}

\section{la'o zoi.\ \F{¯\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \AgdaOperator{\AgdaFunction{¯}} \B r\ .zoi.\ vujnu li no la'oi .\B r.

\begin{code}
¯_ : ℝ → ℝ
¯_ r = Sign.opposite (sign r) , ℤ.∣ ⌊' r ∣ , ⌊'⁻¹ r
\end{code}

\section{la'o zoi.\ \F{fromℝ-}\ .zoi.}
ni'o la'o zoi.\ \F{fromℝ-} \B s \B a \B b\ .zoi.\ pilji lo sumji be la'oi .\B a.\ bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.\ zo'e poi ga jonai ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.+}\ .zoi.\ gi ke'a du li pa gi ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.-}\ .zoi.\ gi ke'a du li ni'u pa

\begin{code}
fromℝ- : Sign → ℕ → (ℕ → Digit 10) → ℝ
fromℝ- s n f = s , n , f
\end{code}

\section{la'o zoi.\ \F{fromℕ} .zoi.}
ni'o la'o zoi.\ \F{fromℕ} \B n\ .zoi.\ namcu du la'oi .\B n.

\begin{code}
fromℕ : ℕ → ℝ
fromℕ n = fromℝ- Sign.+ n $ const 𝔽.zero
\end{code}

\section{la'o zoi.\ \F{fromℤ}\ .zoi.}
ni'o la'o zoi.\ \F{fromℤ} \B z\ .zoi.\ namcu du la'oi .\B z.

\begin{code}
fromℤ : ℤ → ℝ
fromℤ z = fromℝ- (ℤ.sign z) ℤ.∣ z ∣ $ const 𝔽.zero
\end{code}

\section{la'o zoi.\ \F{from𝔽}\ .zoi.}
ni'o la'o zoi.\ \F{from𝔽} \B f\ .zoi.\ namcu du la'oi .\B f.

\begin{code}
from𝔽 : {n : ℕ} → Fin n → ℝ
from𝔽 = {!!}
\end{code}

\section{la'o zoi.\ \F{from𝔻}\ .zoi.}
ni'o la .varik.\ na birti lo du'u ma kau zabna je cu lojbo je cu velcki la'o zoi.\ \F{from𝔻}\ .zoi.  .i ku'i lakne fa lo nu la .varik.\ cu facki

\begin{code}
from𝔻 : Sign → (ℕ → Digit 10) → ℝ
from𝔻 = _⍨ fromℝ- 0
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
_-_ r = r +_ ∘ ¯_
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
ni'o la'o zoi.\ \F{fromℚ} \B k\ .zoi.\ namcu du la'oi .\B k.

\begin{code}
module FromℚI where
  r≈0⇒⌊'r≡0 : _≈ fromℕ 0 ⊆′ (_≡ ℤ.0ℤ) ∘ ⌊'
  r≈0⇒⌊'r≡0 = {!!}

  fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
  fromℕ[s]≉0 = N ∘₂ r≈0⇒⌊'r≡0 ∘ fromℕ ∘ ℕ.suc
    where
    N : {n : ℕ} → ¬_ $ ⌊' (fromℕ $ ℕ.suc n) ≡ ℤ.+ 0
    N ()

fromℚ : ℚ → ℝ
fromℚ (ℚ.mkℚ a b N) = frinu (fromℤ a) 1+b $ fromℕ[s]≉0 b
  where
  open FromℚI
  1+b = fromℕ $ ℕ.suc b
\end{code}

\section{la'oi .\F{Rational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Rational} \B r\ .zoi.\ gi la'oi .\B r.\ frinyna'u  .i cadga fa lo nu li'armi  .i le velcki zo'u lo ro co'e cu frinyna'u jo cu du lo su'o frinu

\begin{code}
Rational : ℝ → Set
Rational r = ∃ $ r ≈_ ∘ fromℚ
\end{code}

\section{la'oi .\F{Irrational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Irrational} \B r\ .zoi.\ gi la'oi .\B r.\ tolfrinyna'u  .i cadga fa lo nu li'armi  .i le velcki zo'u ro da poi ke'a co'e zo'u da tolfrinyna'u jo cu du lo no frinu

\begin{code}
Irrational : ℝ → Set
Irrational = ¬_ ∘ Rational
\end{code}

\section{la'o zoi.\ \F{toℚ}\ .zoi.}
ni'o la'oi .\B r.\ namcu du la'o zoi.\ \F{toℚ} \Sym\{\B r\Sym\} \B R\ .zoi.

\begin{code}
toℚ : {r : ℝ} → Rational r → ℚ
toℚ = proj₁
\end{code}

\section{la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ .zoi.}
ni'o cu'alni la'oi .\B r.\ fa la'o zoi.\ \F{∣\AgdaUnderscore{}∣} \B r\ .zoi.

\begin{code}
∣_∣ : ℝ → ℝ
∣_∣ r = fromℝ- Sign.+ ℤ.∣ ⌊' r ∣ $ ⌊'⁻¹ r
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}⊓\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B r \OpF ⊓ \B s\ .zoi.\ nacmecrai la'oi .\B r.\ ce la'oi .\B s.

\begin{code}
module _⊓_I where
  bool' : ∀ {a} → {A : Set a} → A → A → Bool → A
  bool' r = _⍨ $ if_then_else r

  _≥ᵇ_ : ℝ → ℝ → Bool
  _≥ᵇ_ = {!!}

_⊓_ : ℝ → ℝ → ℝ
_⊓_ r s = bool' r s $ _≥ᵇ_ r s
  where
  open _⊓_I
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}⊔\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B r \OpF ⊔ \B s\ .zoi.\ nacyzmarai la'oi .\B r.\ ce la'oi .\B s.

\begin{code}
_⊔_ : ℝ → ℝ → ℝ
_⊔_ r s = _⊓_I.bool' s r $ _⊓_I._≥ᵇ_ r s
\end{code}

\section{le ctaipe be le su'u mapti}

\begin{code}
module Veritas where
\end{code}

% | ni'o zo'oi .lcblm. cmavlaka'i zo'e ja lu le ctaipe be le su'u mapti li'u
\newcommand\lcblm[1]{le ctaipe be le su'u mapti fa la'o zoi.\ #1\ .zoi.}

\subsection{\lcblm{\F{\AgdaUnderscore{}≈\AgdaUnderscore}}}

\begin{code}
  module _≈_ where
    ≡∧≗⇒≈ : {r s : ℝ}
          → ⌊' r ≡ ⌊' s
          → ⌊'⁻¹ r ≗ ⌊'⁻¹ s
          → r ≈ s
    ≡∧≗⇒≈ = {!!}

    ≡⇒≈ : _≡_ ⇒ _≈_
    ≡⇒≈ = inj₁

    r≈r : Reflexive _≈_
    r≈r = ≡⇒≈ refl

    ≈⇒≈⍨ : _≈_ ⇒ _≈_ ⍨
    ≈⇒≈⍨ = {!!}

    ≈⇒≯ : _≈_ ⇒ ¬_ ∘₂ _>_
    ≈⇒≯ = {!!}

    id≡[≈⇒≈⍨]² : (r s : ℝ) → id ≗ ≈⇒≈⍨ ∘ ≈⇒≈⍨ {r} {s}
    id≡[≈⇒≈⍨]² = {!!}

    ≈∧≈⇒≈ : Transitive _≈_
    ≈∧≈⇒≈ = {!!}

    n,9+≈n+1 : (s : Sign)
             → (n : ℕ)
             → (_≈_
                 (fromℝ- s n $ const 9F)
                 (fromℝ- s (ℕ.suc n) $ const 𝔽.zero))
    n,9+≈n+1 = {!!}

    9≈ : (r s : ℝ)
       → (i : ℕ)
       → ⌊' r ≡ ⌊' s
       → ¬_ $ 9F ≡ ⌊'⁻¹ r i
       → 𝔽.toℕ (⌊'⁻¹ s i) ≡ ℕ.suc (𝔽.toℕ $ ⌊'⁻¹ r i)
       → (_ : (i' : Fin $ i ℕ.+ 1)
            → let i'' = 𝔽.toℕ i' in
              ⌊'⁻¹ r i'' ≡ ⌊'⁻¹ s i'')
       → ((n : ℕ) → ⌊'⁻¹ r (1 ℕ.+ n ℕ.+ i) ≡ 9F)
       → r ≈ s
    9≈ = {!!}

    ¬∃⇒≈ : (r s : ℝ)
          → (¬_ $ ∃ $ λ t → _×_
              (¬_ $ t ≈ fromℕ 0)
              (r ≈ (s + t)))
          → r ≈ s
    ¬∃⇒≈ = {!!}

    ≈⇒¬∃ : (r s : ℝ)
          → r ≈ s
          → (¬_ $ ∃ $ λ t → _×_
              (¬_ $ t ≈ fromℕ 0)
              (r ≈ (s + t)))
    ≈⇒¬∃ = {!!}

    ∣r-s∣>0⇒r≉s : (r s : ℝ) → ∣ r - s ∣ > fromℕ 0 → ¬_ $ r ≈ s
    ∣r-s∣>0⇒r≉s = {!!}

    r≉s⇒∣r-s∣>0 : ¬_ ∘₂ _≈_ ⇒ (_> fromℕ 0) ∘₂ ∣_∣ ∘₂ _-_
    r≉s⇒∣r-s∣>0 = {!!}

    r≈s⇒∣r-s∣≈0 : _≈_ ⇒ (_≈ fromℕ 0) ∘₂ ∣_∣ ∘₂ _-_
    r≈s⇒∣r-s∣≈0 = {!!}

    ∣r-s∣≈0⇒r≈s : (r s : ℝ) → ∣ r - s ∣ ≈ fromℕ 0 → r ≈ s
    ∣r-s∣≈0⇒r≈s = {!!}

    ¬[r≈s⇒fr≈fs] : ¬ ((f : ℝ → ℝ) → _≈_ ⇒ (_≈_ on f))
    ¬[r≈s⇒fr≈fs] = {!!}

    isEquivalence : Relation.Binary.IsEquivalence _≈_
    isEquivalence = record {refl = r≈r; sym = ≈⇒≈⍨; trans = ≈∧≈⇒≈}

    setoid : Setoid _ _
    setoid = record {isEquivalence = isEquivalence}
\end{code}

\subsection{\lcblm{\F{fromℕ}}}

\begin{code}
  module Fromℕ where
    ℤ+_≡⌊'∘fromℕ : (n : ℕ) → ℤ.+_ n ≡ ⌊' (fromℕ n)
    ℤ+_≡⌊'∘fromℕ _ = refl

    ⌊'⁻¹fromℕ≡0 : (m n : ℕ) → 𝔽.zero ≡ ⌊'⁻¹ (fromℕ m) n
    ⌊'⁻¹fromℕ≡0 _ _ = refl

    ℕ≡⇒fromℕ≈ : _≡_ ⇒ (_≈_ on fromℕ)
    ℕ≡⇒fromℕ≈ refl = _≈_.r≈r

    fromℕ≈⇒≡ : (m n : ℕ) → fromℕ m ≈ fromℕ n → m ≡ n
    fromℕ≈⇒≡ = {!!}

    fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
    fromℕ[s]≉0 = FromℚI.fromℕ[s]≉0

    fromℕ-fromℚ : (n : ℕ)
                → let C = Coprime.sym $ Coprime.1-coprimeTo n in
                  fromℕ n ≈ fromℚ (ℚ.mkℚ (ℤ.+ n) 0 C)
    fromℕ-fromℚ n = _≈_.≈⇒≈⍨ $ begin
      fromℚ (ℚ.mkℚ (ℤ.+ n) 0 C) ≈⟨ _≈_.r≈r ⟩
      frinu (fromℤ $ ℤ.+ n) (fromℕ $ ℕ.suc 0) (fromℕ[s]≉0 0) ≈⟨ _≈_.r≈r ⟩
      frinu (fromℕ n) (fromℕ $ ℕ.suc 0) (fromℕ[s]≉0 0) ≈⟨ _≈_.r≈r ⟩
      frinu (fromℕ n) (fromℕ 1) (fromℕ[s]≉0 0) ≈⟨ _≈_.r≈r ⟩
      _ ≈⟨ r≡r/1 _ ▹ sym ▹ _≈_.≡⇒≈ ⟩
      fromℕ n ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      C = Coprime.sym $ 1-coprimeTo _
      r≡r/1 : id ≗ (λ r → frinu r (fromℕ 1) (fromℕ[s]≉0 0))
      r≡r/1 = {!!}

    fromℕ-Rational : (n : ℕ) → Rational $ fromℕ n
    fromℕ-Rational n = ℚ.mkℚ (ℤ.+ n) 0 c , fromℕ-fromℚ n
      where
      c = Coprime.sym $ 1-coprimeTo _

    id≡∣_∣∘⌊'∘fromℕ : id ≗ ℤ.∣_∣ ∘ ⌊' ∘ fromℕ
    id≡∣_∣∘⌊'∘fromℕ _ = refl

    fromℕ≥0 : (n : ℕ) → fromℕ n ≥ fromℕ 0
    fromℕ≥0 0 = inj₁ _≈_.r≈r
    fromℕ≥0 (ℕ.suc n) = inj₂ {!!}
\end{code}

\subsection{\lcblm{\F{fromℤ}}}

\begin{code}
  module Fromℤ where
    id≡⌊'∘fromℤ : (z : ℤ) → z ≡ ⌊' (fromℤ z)
    id≡⌊'∘fromℤ (ℤ.+ _) = refl
    id≡⌊'∘fromℤ ℤ.-[1+ _ ] = refl

    fromℤ-Rational : (z : ℤ) → Rational $ fromℤ z
    fromℤ-Rational z = ℚ.fromℤ z , fromℤ≈fromℚ∘ℤ→ℚ z
      where
      fromℤ≈fromℚ∘ℤ→ℚ : (z : ℤ) → fromℤ z ≈ fromℚ (ℚ.fromℤ z)
      fromℤ≈fromℚ∘ℤ→ℚ z = _≈_.≈⇒≈⍨ $ begin
        fromℚ (ℚ.fromℤ z) ≈⟨ _≈_.r≈r ⟩
        fromℚ (ℚ.mkℚ z 0 C) ≈⟨ _≈_.r≈r ⟩
        frinu (fromℤ z) (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0) ≈⟨ _≈_.r≈r ⟩
        _ ≈⟨ _≈_.≡⇒≈ $ sym $ r≡r/1 $ fromℤ z ⟩
        fromℤ z ∎
        where
        C = Coprime.sym $ 1-coprimeTo _
        open import Relation.Binary.Reasoning.Setoid _≈_.setoid
        r≡r/1 : id ≗ (λ r → frinu r (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0))
        r≡r/1 = {!!}

    fromℤ≡+fromℕ : (z : ℤ)
                 → ℤ.sign z ≡ Sign.+
                 → fromℤ z ≡ fromℕ ℤ.∣ z ∣
    fromℤ≡+fromℕ (ℤ.+ z) d = refl

    fromℤ≡¯fromℕ : (z : ℤ)
                 → ℤ.sign z ≡ Sign.-
                 → fromℤ z ≡ ¯ fromℕ ℤ.∣ z ∣
    fromℤ≡¯fromℕ ℤ.-[1+ _ ] _ = refl
\end{code}

\subsection{\lcblm{\F{¯\AgdaUnderscore}}}

\begin{code}
  module ¯_ where
    r≈-r⇒r≈0 : (λ r → r ≈ ¯_ r) ⊆′ _≈ fromℕ 0
    r≈-r⇒r≈0 = {!!}

    r>0⇒¯r≈¯r : (r : ℝ)
              → r > fromℕ 0
              → ¯_ r ≈ fromℝ- Sign.- ℤ.∣ ⌊' r ∣ (⌊'⁻¹ r)
    r>0⇒¯r≈¯r = {!!}

    r<0⇒¯r≈∣r∣ : fromℕ 0 >_ ⊆′ (λ r → ¯_ r ≈ ∣ r ∣)
    r<0⇒¯r≈∣r∣ = {!!}

    r-¯s≈r+s : (r s : ℝ) → (r - (¯ s)) ≈ (r + s)
    r-¯s≈r+s = λ r s → begin
      r - ¯_ s ≈⟨ _≈_.r≈r ⟩
      r + (¯ ¯_ s) ≈⟨ {!!} ⟩
      r + s ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    r≈s⇒¯r≈¯s : Algebra.Congruent₁ _≈_ ¯_
    r≈s⇒¯r≈¯s = {!!}

    r≡¯¯r : id ≗ (¯_ ∘ ¯_)
    r≡¯¯r = {!!}

    R[¯R] : Rational ⊆ Rational ∘ ¯_
    R[¯R] = {!!}

    R[¯r]⇒R[r] : Rational ∘ ¯_ ⊆′ Rational
    R[¯r]⇒R[r] = {!!}

    I[¯I] : Irrational ⊆′ Irrational ∘ ¯_
    I[¯I] = {!!}

    I[¯r]⇒I[r] : Irrational ∘ ¯_ ⊆′ Irrational
    I[¯r]⇒I[r] = {!!}

    0≈-0 : fromℕ 0 ≈ (¯ fromℕ 0)
    0≈-0 = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}+\AgdaUnderscore}}}

\begin{code}
  module _+_ where
    module VI where
      I[r]∧r≈s⇒I[s] : {r s : ℝ} → Irrational r → r ≈ s → Irrational s
      I[r]∧r≈s⇒I[s] = {!!}

    +≈+⍨ : Commutative _≈_ _+_
    +≈+⍨ = {!!}

    +-ass : Associative _≈_ _+_
    +-ass = {!!}

    id≡+0 : Identity _≡_ (fromℕ 0) _+_
    id≡+0 = {!!} , {!!}

    id≈+0 : Identity _≈_ (fromℕ 0) _+_
    id≈+0 = id≡+0 ▹ Σ.map (_≈_.≡⇒≈ ∘_)  (_≈_.≡⇒≈ ∘_)

    dratadratas : (r s : ℝ)
                → ¬_ $ r ≈ fromℕ 0 × s ≈ fromℕ 0
                → let N = ¬_ ∘ _≈ (r + s) in
                  N r × N s
    dratadratas = {!!}

    r≡⌊'r+⌊'⁻¹r : (r : ℝ) → r ≡ fromℤ (⌊' r) + ⌊'⁻¹ℝ r
    r≡⌊'r+⌊'⁻¹r = {!!}

    r≡⌊'⁻¹r+⌊'r : id ≗ (λ r → ⌊'⁻¹ℝ r + fromℤ (⌊' r))
    r≡⌊'⁻¹r+⌊'r = {!!}

    r≡f+z : (s : Sign)
          → (n : ℕ)
          → (f : ℕ → Digit 10)
          → fromℝ- s n f ≡ from𝔻 s f + fromℤ (s ℤ.◃ n)
    r≡f+z = {!!}

    ℕ+ : (m n : ℕ) → fromℕ m + fromℕ n ≡ fromℕ (m ℕ.+ n)
    ℕ+ = {!!}

    ℤ+ : (x z : ℤ) → fromℤ x + fromℤ z ≡ fromℤ (x ℤ.+ z)
    ℤ+ = {!!}

    ℚ+ : (k l : ℚ) → fromℚ k + fromℚ l ≡ fromℚ (k ℚ.+ l)
    ℚ+ = {!!}

    r≈r+s⇒s≈0 : (λ r s → r ≈ (r + s)) ⇒ (λ r s → s ≈ fromℕ 0)
    r≈r+s⇒s≈0 = {!!}

    r≉r+s : (r s : ℝ) → ¬_ $ s ≈ fromℕ 0 → ¬_ $ r ≈ (r + s)
    r≉r+s _ _ = _∘ r≈r+s⇒s≈0

    r+s≈r'+s' : Algebra.Congruent₂ _≈_ _+_
    r+s≈r'+s' = {!!}

    r+s≈r'+s : {r r' s : ℝ} → r ≈ r' → (r + s) ≈ (r' + s)
    r+s≈r'+s {s = s} = (r+s≈r'+s' {v = s} ⍨) _≈_.r≈r

    r+s≈r+s' : {r s s' : ℝ} → s ≈ s' → (r + s) ≈ (r + s')
    r+s≈r+s' {r} = r+s≈r'+s' {r} _≈_.r≈r

    ¯r+¯s≈¯[r+s] : (r s : ℝ) → (¯_ r + ¯_ s) ≈ ¯_ (r + s)
    ¯r+¯s≈¯[r+s] = {!!}

    ℚ+' : {r s : ℝ}
        → (R : Rational r)
        → (S : Rational s)
        → (r + s) ≈ fromℚ (proj₁ R ℚ.+ proj₁ S)
    ℚ+' {r} {s} R S = begin
      r + s ≈⟨ r+s≈r'+s' (proj₂ R) $ proj₂ S ⟩
      fromℚ (proj₁ R) + fromℚ (proj₁ S) ≈⟨ _≈_.r≈r ⟩
      _ ≈⟨ ℚ+ (proj₁ R) (proj₁ S) ▹ _≈_.≡⇒≈ ⟩
      fromℚ (proj₁ R ℚ.+ proj₁ S) ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    R[R+R] : (r s : ℝ) → Rational r → Rational s → Rational $ r + s
    R[R+R] r s R@(r' , _) S@(s' , _) = r' ℚ.+ s' , ℚ+' R S

    I[I+R] : {r s : ℝ} → Irrational r → Rational s → Irrational $ r + s
    I[I+R] = {!!}

    I[R+I] : {r s : ℝ} → Rational r → Irrational s → Irrational $ r + s
    I[R+I] {r} {s} R S = VI.I[r]∧r≈s⇒I[s] (I[I+R] S R) $ +≈+⍨ s r

    I[r+s]⇒I[r]∨I[s] : (r s : ℝ)
                     → Irrational $ r + s
                     → Irrational r ∨ Irrational s
    I[r+s]⇒I[r]∨I[s] = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}-\AgdaUnderscore}}}

\begin{code}
  module _-_ where
    0≈r-s : _≈_ ⇒ (fromℕ 0 ≈_) ∘₂ _-_
    0≈r-s = {!!}

    0≈r-r : (r : ℝ) → fromℕ 0 ≈ (r - r)
    0≈r-r r = 0≈r-s {r} _≈_.r≈r

    r≡r-0 : Algebra.RightIdentity _≡_ (fromℕ 0) _-_
    r≡r-0 = {!!}

    r≈r-0 : (r 0' : ℝ) → 0' ≈ fromℕ 0 → r ≈ (r - 0')
    r≈r-0 = {!!}

    -r≈0-r : (r 0' : ℝ) → 0' ≈ fromℕ 0 → ¯_ r ≈ (0' - r)
    -r≈0-r = {!!}

    r-s-t≈r-[s+t] : (r s t : ℝ) → ((r - s) - t) ≈ (r - (s + t))
    r-s-t≈r-[s+t] r s t = begin
      (r - s) - t ≈⟨ r≈r ⟩
      (r - s) + (¯ t) ≈⟨ r≈r ⟩
      (r + (¯ s)) + (¯ t) ≈⟨ _+_.+-ass r (¯ s) (¯ t) ⟩
      r + ((¯ s) + (¯ t)) ≈⟨ ¯r+¯s≈¯[r+s] s t ▹ _+_.r+s≈r+s' {r} ⟩
      r + (¯ (s + t)) ≈⟨ r≈r ⟩
      r - (s + t) ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      open _+_ using (¯r+¯s≈¯[r+s]; r+s≈r'+s')
      open _≈_ using (r≈r)

    r-s≈r'-s' : Algebra.Congruent₂ _≈_ _-_
    r-s≈r'-s' {r} {r'} {s} {s'} d₁ d₂ = begin
      r - s ≈⟨ _≈_.r≈r ⟩
      r + (¯ s) ≈⟨ _+_.r+s≈r'+s {s = ¯ s} d₁ ⟩
      r' + (¯ s) ≈⟨ ¯_.r≈s⇒¯r≈¯s d₂ ▹ _+_.r+s≈r+s' {r'} ⟩
      r' + (¯ s') ≈⟨ _≈_.r≈r ⟩
      r' - s' ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    r-s≈r-s' : {r s s' : ℝ} → s ≈ s' → (r - s) ≈ (r - s')
    r-s≈r-s' = {!!}

    r-s≈r'-s : {r r' s : ℝ} → r ≈ r' → (r - s) ≈ (r' - s)
    r-s≈r'-s = {!!}

    r≈[r-s]+s : (r s : ℝ) → r ≈ (s + (r - s))
    r≈[r-s]+s r s = _≈_.≈⇒≈⍨ $ begin
      s + (r - s) ≈⟨ +≈+⍨ s $ r - s ⟩
      (r - s) + s ≈⟨ _≈_.r≈r ⟩
      (r + (¯ s)) + s ≈⟨ +-ass r (¯ s) s ⟩
      r + ((¯ s) + s) ≈⟨ +≈+⍨ (¯ s) s ▹ r+s≈r+s' {r} ⟩
      r + (s + (¯ s)) ≈⟨ _≈_.r≈r ⟩
      r + (s - s) ≈⟨ 0≈r-r s ▹ _≈_.≈⇒≈⍨ ▹ r+s≈r+s' {r} ⟩
      r + fromℕ 0 ≈⟨ proj₂ _+_.id≈+0 r ⟩
      r ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      open _+_
        using (
          r+s≈r'+s';
          r+s≈r+s';
          +-ass;
          +≈+⍨
        )

    r≈0-[0-r] : (r : ℝ) → r ≈_ $ fromℕ 0 -_ $ fromℕ 0 - r
    r≈0-[0-r] r = _≈_.≈⇒≈⍨ $ begin
      fromℕ 0 - (fromℕ 0 - r) ≈⟨ r≈r ⟩
      _ ≈⟨ -r≈0-r r _ r≈r ▹ r-s≈r-s' {fromℕ 0} ▹ _≈_.≈⇒≈⍨ ⟩
      fromℕ 0 - (¯ r) ≈⟨ -r≈0-r _ _ r≈r ▹ _≈_.≈⇒≈⍨ ⟩
      ¯ (¯ r) ≈⟨ ¯_.r≡¯¯r _ ▹ sym ▹ _≈_.≡⇒≈ ⟩
      r ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      open _≈_ using (r≈r)

    0≈r+[0-r] : (r 0' : ℝ) → 0' ≈ fromℕ 0 → fromℕ 0 ≈_ $ r + (0' - r)
    0≈r+[0-r] r 0' d = _≈_.≈⇒≈⍨ $ begin
      r + (0' - r) ≈⟨ -r≈0-r r _ d ▹ _≈_.≈⇒≈⍨ ▹ r+s≈r+s' {r} ⟩
      r + ¯_ r ≈⟨ _≈_.r≈r ⟩
      r - r ≈⟨ 0≈r-r r ▹ _≈_.≈⇒≈⍨ ⟩
      fromℕ 0 ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      open _+_ using (r+s≈r+s')

    r>r-s : (r s : ℝ) → s > fromℕ 0 → r > (r - s)
    r>r-s = {!!}

    r≥r-s : (r s : ℝ) → s ≥ fromℕ 0 → r ≥ (r - s)
    r≥r-s r s (inj₁ d) = inj₁ $ r≈r-0 r s d
    r≥r-s r s (inj₂ z) = inj₂ $ r>r-s r s z

    I[I-R] : (r s : ℝ) → Irrational r → Rational s → Irrational $ r - s
    I[I-R] = {!!}

    I[R-I] : {r s : ℝ} → Rational r → Irrational s → Irrational $ r - s
    I[R-I] R = _+_.I[R+I] R ∘ ¯_.I[¯I] _

    R[R-R] : (r s : ℝ) → Rational r → Rational s → Rational $ r - s
    R[R-R] r s R S = _+_.R[R+R] r (¯ s) R {!!}
\end{code}

\subsection{\lcblm{\F{from𝔻}}}

\begin{code}
  module From𝔻 where
    id≡sign∘from𝔻⍨ : (s : Sign) → (f : _) → s ≡ sign (from𝔻 s f)
    id≡sign∘from𝔻⍨ _ _ = refl

    id≡⌊'⁻¹∘from𝔻s : (s : Sign) → (f : _) → f ≡ ⌊'⁻¹ (from𝔻 s f)
    id≡⌊'⁻¹∘from𝔻s _ _ = refl

    0≡⌊'[from𝔻] : (s : Sign)
                → (f : ℕ → Digit 10)
                → ℤ.+ 0 ≡ ⌊' (from𝔻 s f)
    0≡⌊'[from𝔻] = λ {Sign.+ _ → refl; Sign.- _ → refl}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}*\AgdaUnderscore}}}

\begin{code}
  module _*_ where
    r≈1*r : Identity _≈_ (fromℕ 1) _*_
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
                (from𝔻 (sign r) {!!})
                (fromℤ $ ℤ._+_
                  (⌊' r ℤ.* ℤ.+ 10)
                  {!!})))
    r*n≈? = {!!}

    r*10≈_ : (r : ℝ)
           → (_≈_
               (r * fromℕ 10)
               (_+_
                 (sign r , 0 , ⌊'⁻¹ r ∘ ℕ.suc)
                 (fromℤ $ ℤ._+_
                   (⌊' r ℤ.* ℤ.+_ 10)
                   (signℤ r ℤ.*_ $ ℤ.+_ $ 𝔽.toℕ $ ⌊'⁻¹ r 0))))
    r*10≈_ = {!!}

    r*s>r : (r s : ℝ)
          → r > fromℕ 0
          → s > fromℕ 0
          → (r * s) > r
    r*s>r = {!!}

    r>r*s : (r s : ℝ)
          → r > fromℕ 0
          → ∣ s ∣ < fromℕ 1
          → r > (r * s)
    r>r*s = {!!}

    I[I*R] : (r s : ℝ) → Irrational r → Rational s → Irrational $ r * s
    I[I*R] = {!!}

    R[R*R] : (r s : ℝ) → Rational r → Rational s → Rational $ r * s
    R[R*R] = {!!}

    ∃[R[I*I]] : (Σ.Σ (_ × _) $ λ (r , s) →
                  (Irrational r × Irrational s) × Rational (r * s))
    ∃[R[I*I]] = (√2 , _) , ((λ x → x , x) {!!}) , R
      where
      ½ = frinu (fromℕ 1) (fromℕ 2) (Fromℕ.fromℕ[s]≉0 1)
      √2 = fromℕ 2 ^ ½
      R = R[r]∧r≈s⇒R[s] (Fromℕ.fromℕ-Rational 2) d
        where
        R[r]∧r≈s⇒R[s] : {r s : ℝ} → Rational r → r ≈ s → Rational s
        R[r]∧r≈s⇒R[s] = {!!}
        d = _≈_.≈⇒≈⍨ $ begin
          √2 * √2 ≈⟨ _≈_.r≈r ⟩
          (fromℕ 2 ^ ½) * (fromℕ 2 ^ ½) ≈⟨ _≈_.r≈r ⟩
          _ ≈⟨ [r^s]*[r^t]≈r^[s+t] (fromℕ 2) ½ ½ ⟩
          fromℕ 2 ^ (½ + ½) ≈⟨ _≈_.r≈r ⟩
          _ ≈⟨ {!!} ▹ s≈s'⇒r^s≈r^s' (fromℕ 2) {½ + ½} {fromℕ 1} ⟩
          fromℕ 2 ^ fromℕ 1 ≈⟨ r≈r^1 (fromℕ 2) ▹ _≈_.≈⇒≈⍨ ⟩
          fromℕ 2 ∎
          where
          open import Relation.Binary.Reasoning.Setoid _≈_.setoid
          r≈r^1 : (r : ℝ) → r ≈ (r ^ fromℕ 1)
          r≈r^1 = {!!}
          s≈s'⇒r^s≈r^s' : (r : ℝ)
                        → {s s' : ℝ}
                        → s ≈ s'
                        → (r ^ s) ≈ (r ^ s')
          s≈s'⇒r^s≈r^s' = {!!}
          [r^s]*[r^t]≈r^[s+t] : (r s t : ℝ)
                              → ((r ^ s) * (r ^ t)) ≈ (r ^ (s + t))
          [r^s]*[r^t]≈r^[s+t] = {!!}

    r*s≈r'*s' : Algebra.Congruent₂ _≈_ _*_
    r*s≈r'*s' = {!!}

    r*s≈r*s' : {r s s' : ℝ} → s ≈ s' → (r * s) ≈ (r * s')
    r*s≈r*s' {r} = r*s≈r'*s' {r} _≈_.r≈r

    r*s≈r'*s : {r r' s : ℝ} → r ≈ r' → (r * s) ≈ (r' * s)
    r*s≈r'*s {s = s} = (r*s≈r'*s' ⍨) $ _≈_.r≈r {s}

    ℕ* : (m n : ℕ) → fromℕ m * fromℕ n ≡ fromℕ (m ℕ.* n)
    ℕ* = {!!}

    ℤ* : (x z : ℤ) → fromℤ x * fromℤ z ≡ fromℤ (x ℤ.* z)
    ℤ* = {!!}

    ℚ* : (k l : ℚ) → fromℚ k * fromℚ l ≡ fromℚ (k ℚ.* l)
    ℚ* = {!!}

    R[r]∧R[s]⇒R[r*s] : let R = Rational in
                        {r s : ℝ} → R r → R s → R $ r * s
    R[r]∧R[s]⇒R[r*s] {r} {s} (R , dr) (S , ds) = R ℚ.* S , d
      where
      d = begin
        r * s ≈⟨ r*s≈r'*s' dr ds ⟩
        fromℚ R * fromℚ S ≈⟨ ℚ* R S ▹ _≈_.≡⇒≈ ⟩
        fromℚ (R ℚ.* S) ∎
        where
        open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    n*r≈+/n/r : (n : ℕ)
              → (r : ℝ)
              → (_≈_
                  (fromℕ n * r)
                  (𝕃.foldr _+_ (fromℕ 0) $ 𝕃.replicate n r))
    n*r≈+/n/r = {!!}

    dist : Algebra._DistributesOver_ _≈_ _*_ _+_
    dist = {!!}

    *-magma : Algebra.IsMagma _≈_ _*_
    *-magma = record {
      isEquivalence = _≈_.isEquivalence;
      ∙-cong = r*s≈r'*s'}
\end{code}

\subsection{\lcblm{\F{frinu}}}

\begin{code}
  module Frinu where
    module I where
      r>1⇒r≉0 : _> fromℕ 1 ⊆ ¬_ ∘ _≈ fromℕ 0
      r>1⇒r≉0 {r} = >⇒≉ ∘ r>1⇒r>0 {r}
        where
        >⇒≉ : _>_ ⇒ ¬_ ∘₂ _≈_
        >⇒≉ = {!!}
        r>1⇒r>0 : _> fromℕ 1 ⊆ _> fromℕ 0
        r>1⇒r>0 = {!!}

      ¯r≈0⇒r≈0 : (_≈ fromℕ 0) ∘ ¯_ ⊆′ _≈ fromℕ 0
      ¯r≈0⇒r≈0 = {!!}

    r/r≡1 : (r : ℝ) → (N : _) → frinu r r N ≡ fromℕ 1
    r/r≡1 = {!!}

    r≡r/1 : (r : ℝ) → r ≡ frinu r (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0)
    r≡r/1 = {!!}

    ∣s∣>∣t∣⇒∣r/s∣>∣r/t∣ : (r s t : ℝ)
                        → (Ns : _)
                        → (Nt : _)
                        → ∣ s ∣ > ∣ t ∣
                        → ¬_ $ r ≈ fromℕ 0
                        → frinu r s Ns > frinu r s Nt
    ∣s∣>∣t∣⇒∣r/s∣>∣r/t∣ = {!!}

    0≈0/r : (r s : ℝ)
          → (N : _)
          → s ≈ fromℕ 0
          → fromℕ 0 ≈ frinu s r N
    0≈0/r = {!!}

    0'≈0'/r : (r 0' : ℝ)
            → (N : _)
            → 0' ≈ fromℕ 0
            → 0' ≈ frinu 0' r N
    0'≈0'/r _ = (_≈_.≈∧≈⇒≈ ˢ_) ∘₂ 0≈0/r _

    ∣r/s∣<∣r∣ : (r s : ℝ)
              → ¬_ $ r ≈ fromℕ 0
              → (z : s > fromℕ 1)
              → ∣ r ∣ > ∣ frinu r s $ I.r>1⇒r≉0 z ∣
    ∣r/s∣<∣r∣ = {!!}

    ∣r∣<∣r/s∣ : (r s : ℝ)
            → (N : _)
            → ¬_ $ r ≈ fromℕ 0
            → ∣ s ∣ < fromℕ 1
            → ∣ r ∣ < ∣ frinu r s N ∣
    ∣r∣<∣r/s∣ = {!!}

    ∣r/s∣≤∣r∣ : (r s : ℝ)
              → (z : s > fromℕ 1)
              → ∣ r ∣ ≥ ∣ frinu r s $ I.r>1⇒r≉0 z ∣
    ∣r/s∣≤∣r∣ = {!!}

    -r/-s<-r : (r s : ℝ)
             → (z : s > fromℕ 1)
             → ¯_ r > frinu (¯ r) (¯ s) (I.r>1⇒r≉0 z ∘ I.¯r≈0⇒r≈0 _)
    -r/-s<-r = {!!}

    r<r/s : (r s : ℝ)
          → (N : _)
          → fromℕ 1 > s
          → s > fromℕ 0
          → r > frinu r s N
    r<r/s = {!!}

    -r/-s≈r/s : (r s : ℝ)
              → (N : _)
              → (N' : _)
              → frinu (¯ r) (¯ s) N ≈ frinu r s N'
    -r/-s≈r/s = {!!}

    ℕ/ : (m n : ℕ)
       → (N : _)
       → (N' : _)
       → fromℤ (⌊' (frinu (fromℕ m) (fromℕ n) N')) ≈ fromℕ (ℕ._/_ m n {N})
    ℕ/ = {!!}

    ℤ/ : (x z : ℤ)
       → (N : _)
       → (N' : _)
       → (_≈_
           (fromℤ $ ⌊' $ frinu (fromℤ x) (fromℤ z) N')
           (fromℤ $ ℤ._div_ x z {N}))
    ℤ/ = {!!}

    ℚ/ : (k l : ℚ)
       → (N : _)
       → (N' : _)
       → (_≈_
           (frinu (fromℚ k) (fromℚ l) N')
           (fromℚ (ℚ._÷_ k l {N})))
    ℚ/ = {!!}

    ℚ/' : (z : ℤ)
        → (n : ℕ)
        → (_≈_
            (fromℚ $ z ℚ./ ℕ.suc n)
            (frinu (fromℤ z) (fromℕ $ ℕ.suc n) $ Fromℕ.fromℕ[s]≉0 n))
    ℚ/' z n = begin
      fromℚ (z ℚ./ ℕ.suc n) ≈⟨ {!!} ⟩
      fromℚ (ℚ.fromℤ z ℚ.÷ (ℚ.fromℤ $ ℤ.+ ℕ.suc n)) ≈⟨ {!!} ⟩
      frinu (fromℤ z) (fromℕ $ ℕ.suc n) (Fromℕ.fromℕ[s]≉0 n) ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    R[ℕ/ℕ] : (m n : ℕ)
           → (N : _)
           → Rational $ frinu (fromℕ m) (fromℕ $ ℕ.suc n) N
    R[ℕ/ℕ] m n N = m' ℚ.÷ n'++ , d
      where
      m' = ℚ.fromℤ $ ℤ.+ m
      n'++ = ℚ.fromℤ (ℤ.+ ℕ.suc n)
      d = ℕ/' m n N
        where
        ℕ/' : (m n : ℕ)
            → (N : _)
            → (_≈_
                (frinu (fromℕ m) (fromℕ $ ℕ.suc n) N)
                (fromℚ $ ℚ.fromℤ (ℤ.+ m) ℚ.÷ ℚ.fromℤ (ℤ.+ ℕ.suc n)))
        ℕ/' = {!!}

    R[ℤ/ℕ] : (z : ℤ)
           → (n : ℕ)
           → (N : _)
           → Rational $ frinu (fromℤ z) (fromℕ n) N
    R[ℤ/ℕ] = {!!}

    R[ℚ/ℕ] : (k : ℚ)
           → (n : ℕ)
           → (N : _)
           → Rational $ frinu (fromℚ k) (fromℕ n) N
    R[ℚ/ℕ] = {!!}

    R[ℤ/ℤ] : (x z : ℤ)
           → (N : _)
           → Rational $ frinu (fromℤ x) (fromℤ z) N
    R[ℤ/ℤ] = {!!}

    r≈s*r/s : (r s : ℝ) → (N : _) → r ≈ (s * frinu r s N)
    r≈s*r/s = {!!}

    r/s≈r'/s' : {r r' s s' : ℝ}
              → (N : _)
              → (N' : _)
              → r ≈ r'
              → s ≈ s'
              → frinu r s N ≈ frinu r' s' N'
    r/s≈r'/s' = {!!}

    r/s≈r'/s : {r r' s : ℝ}
             → (N : _)
             → r ≈ r'
             → frinu r s N ≈ frinu r' s N
    r/s≈r'/s N = (r/s≈r'/s' N N ⍨) _≈_.r≈r

    r/s≈r/s' : {r s s' : ℝ}
             → (N : _)
             → (N' : _)
             → s ≈ s'
             → frinu r s N ≈ frinu r s' N'
    r/s≈r/s' {r} N N' = r/s≈r'/s' {r} N N' _≈_.r≈r
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}\textasciicircum\AgdaUnderscore}}}

\begin{code}
  module _^_ where
    id≡_^1 : Algebra.RightIdentity _≡_ (fromℕ 1) _^_
    id≡_^1 = {!!}

    1≡1^r : const (fromℕ 1) ≗ fromℕ 1 ^_
    1≡1^r = {!!}

    1≡r^0 : (r 0' : ℝ) → 0' ≈ fromℕ 0 → fromℕ 1 ≡ r ^ 0'
    1≡r^0 = {!!}

    0≈0^r : (r s : ℝ)
          → ¬_ $ r ≈ fromℕ 0
          → s ≈ fromℕ 0
          → fromℕ 0 ≈ (s ^ r)
    0≈0^r = {!!}

    1≡0^0 : fromℕ 1 ≡ fromℕ 0 ^ fromℕ 0
    1≡0^0 = 1≡r^0 (fromℕ 0) _ _≈_.r≈r

    [r^s]^t≈r^[s*t] : (r s t : ℝ) → ((r ^ s) ^ t) ≈ (r ^ (s * t))
    [r^s]^t≈r^[s*t] = {!!}

    r≈[r^s]^[1/s] : (r s : ℝ)
                  → (N : _)
                  → r ≈_ $ (r ^ s) ^ frinu (fromℕ 1) s N
    r≈[r^s]^[1/s] = {!!}

    R[R^ℕ] : (r : ℝ) → (n : ℕ) → Rational r → Rational $ r ^ fromℕ n
    R[R^ℕ] r 0 R = _,_ ℚ.1ℚ $ begin
      r ^ fromℕ 0 ≈⟨ 1≡r^0 r _ _≈_.r≈r ▹ sym ▹ _≈_.≡⇒≈ ⟩
      fromℕ 1 ≈⟨ Fromℕ.fromℕ-fromℚ 1 ⟩
      fromℚ (ℚ.mkℚ (ℤ.+ 1) 0 C) ≈⟨ _≈_.r≈r ⟩
      fromℚ ℚ.1ℚ ∎
      where
      C = Coprime.sym $ 1-coprimeTo _
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
    R[R^ℕ] r (ℕ.suc n) R = proj₁ R ℚ.* proj₁ (R[R^ℕ] _ n R) , {!!}

    ∃R[I^R] : (Σ.Σ
                 (ℝ × ℝ)
                 (λ (r , s) → (Irrational r × Rational s) × Rational (r ^ s)))
    ∃R[I^R] = (√2 , fromℕ 2) , ({!!} , R[ℕ] 2) , {!!}
      where
      R[ℕ] = Fromℕ.fromℕ-Rational
      √2 = fromℕ 2 ^ frinu (fromℕ 1) (fromℕ 2) N
        where
        N = (¬ (2 ≡ 0) ∋ λ ()) ∘ Fromℕ.fromℕ≈⇒≡ _ _

    ∃I[R^R] : (Σ.Σ
                 (_ × _)
                 (λ (r , s) →
                   (_×_
                     (Rational r × Rational s)
                     (Irrational $ r ^ s))))
    ∃I[R^R] = (fromℕ 2 , ½) , (R[ℕ] _ , Frinu.R[ℕ/ℕ] 1 1 2≉0) , I
      where
      I = proj₁ $ proj₁ $ proj₂ ∃R[I^R]
      R[ℕ] = Fromℕ.fromℕ-Rational
      2≉0 = (¬ (2 ≡ 0) ∋ λ ()) ∘ Fromℕ.fromℕ≈⇒≡ _ _
      ½ = frinu (fromℕ 1) (fromℕ 2) 2≉0

    R[R^r] : (r s : ℝ)
           → Rational r
           → Set ∋ {!!}
           → Rational $ r ^ s
    R[R^r] = {!!}

    I[2^[1/2]] : let 2≉0 = ((¬ (2 ≡ 0) ∋ λ ()) ∘ Fromℕ.fromℕ≈⇒≡ 2 0) in
                 (Irrational $
                   (fromℕ 2 ^ frinu (fromℕ 1) (fromℕ 2) 2≉0))
    I[2^[1/2]] = proj₁ $ proj₁ $ proj₂ ∃R[I^R]

    ℕ^ : (m n : ℕ)
       → (_≈_
           (fromℕ m ^ fromℕ n)
           (fromℕ $ m ℕ.^ n))
    ℕ^ = {!!}

    R[ℕ^ℕ] : (m n : ℕ) → Rational $ fromℕ m ^ fromℕ n
    R[ℕ^ℕ] = {!!}

    R[ℤ^ℤ] : (x z : ℤ) → Rational $ fromℤ x ^ fromℤ z
    R[ℤ^ℤ] = {!!}

    ∣r∣>1∧s>1⇒∣r∣>∣r^s∣ : (r s : ℝ)
                        → ∣ r ∣ > fromℕ 1
                        → s > fromℕ 1
                        → ∣ r ∣ < ∣ r ^ s ∣
    ∣r∣>1∧s>1⇒∣r∣>∣r^s∣ = {!!}

    r>0∧r<1∧s>1⇒r>r^s : (r s : ℝ)
                      → r > fromℕ 0
                      → r < fromℕ 1
                      → s > fromℕ 1
                      → r > (r ^ s)
    r>0∧r<1∧s>1⇒r>r^s = {!!}

    rel : (r s : ℝ)
        → ∣ r ∣ < fromℕ 1
        → s > fromℕ 1
        → ∣ r ∣ < ∣ r ^ s ∣
    rel = {!!}

    r^s≈r'^s' : Algebra.Congruent₂ _≈_ _^_
    r^s≈r'^s' = {!!}
\end{code}

\subsection{\lcblm{\F{⌊'}}}

\begin{code}
  module ⌊' where
    fromℤ∘⌊' : (r : ℝ) → ⌊'⁻¹ r ≗ const 𝔽.zero → r ≡ fromℤ (⌊' r)
    fromℤ∘⌊' = {!!}

    fromℤ∘⌊'' : (r : ℝ) → r ≡ fromℤ (⌊' r) → ⌊'⁻¹ r ≗ const 𝔽.zero
    fromℤ∘⌊'' = {!!}

    ⌊'∘fromℤ : (z : ℤ) → z ≡ ⌊' (fromℤ z)
    ⌊'∘fromℤ = {!!}

    ∃f≡ : (r : ℝ) → ∃ $ _≡_ r ∘ _+ fromℤ (⌊' r)
    ∃f≡ r = ⌊'⁻¹ℝ r , _+_.r≡⌊'⁻¹r+⌊'r r

    sign∘fromℤ : ℤ.sign ≗ (sign ∘ fromℤ)
    sign∘fromℤ _ = refl
\end{code}

\subsection{\lcblm{\F{⌊'⁻¹ℝ}}}

\begin{code}
  module ⌊'⁻¹ℝ where
    I⇒I[⌊'⁻¹ℝ] : Irrational ⊆ Irrational ∘ ⌊'⁻¹ℝ
    I⇒I[⌊'⁻¹ℝ] = {!!}

    I[⌊'⁻¹ℝ]⇒I : Irrational ∘ ⌊'⁻¹ℝ ⊆ Irrational
    I[⌊'⁻¹ℝ]⇒I = {!!}

    R⇒R[⌊'⁻¹ℝ] : Rational ⊆ Rational ∘ ⌊'⁻¹ℝ
    R⇒R[⌊'⁻¹ℝ] = {!!}

    R[⌊'⁻¹ℝ]⇒R : (r : ℝ) → Rational $ ⌊'⁻¹ℝ r → Rational r
    R[⌊'⁻¹ℝ]⇒R = {!!}

    ⌊'⁻¹ℝ≡⌊'⁻¹ℝ∘⌊'⁻¹ℝ : Algebra.IdempotentFun _≡_ ⌊'⁻¹ℝ
    ⌊'⁻¹ℝ≡⌊'⁻¹ℝ∘⌊'⁻¹ℝ _ = refl

    ⌊'⁻¹ℝ∘fromℕ : (n : ℕ) → ⌊'⁻¹ℝ (fromℕ n) ≈ fromℕ 0
    ⌊'⁻¹ℝ∘fromℕ = {!!}

    from𝔻s≡⌊'⁻¹ℝ∘from𝔻s : (s : Sign)
                        → (f : ℕ → Digit 10)
                        → from𝔻 s f ≡ ⌊'⁻¹ℝ (from𝔻 s f)
    from𝔻s≡⌊'⁻¹ℝ∘from𝔻s _ _ = refl
\end{code}

\subsection{\lcblm{\F{sign}}}

\begin{code}
  module SignV where
    r>0⇒s[r]≡+ : _> fromℕ 0 ⊆′ (_≡ Sign.+) ∘ sign
    r>0⇒s[r]≡+ = {!!}

    r<0⇒s[r]≡- : _< fromℕ 0 ⊆′ (_≡ Sign.-) ∘ sign
    r<0⇒s[r]≡- = {!!}

    r≉0∧s[r]≡+⇒r>0 : (_⊆′_
                        (λ r → (¬_ $ r ≈ fromℕ 0) × sign r ≡ Sign.+)
                        (_> fromℕ 0))
    r≉0∧s[r]≡+⇒r>0 = {!!}

    r≉0∧s[r]≡-⇒r<0 : (_⊆′_
                        (λ r → (¬_ $ r ≈ fromℕ 0) × sign r ≡ Sign.-)
                        (_< fromℕ 0))
    r≉0∧s[r]≡-⇒r<0 = {!!}

    s[r]≡+⇒r≥0 : (_≡ Sign.+) ∘ sign ⊆′ _≥ fromℕ 0
    s[r]≡+⇒r≥0 = {!!}

    jonis : ∀ {p₁ p₂ } → {P₁ : Pred ℝ p₁} → {P₂ : Pred ℝ p₂}
          → ({r : ℝ} → P₁ r → sign r ≡ Sign.+ → P₂ r)
          → ({r : ℝ} → P₁ r → sign r ≡ Sign.- → P₂ r)
          → (r : ℝ)
          → P₁ r
          → P₂ r
    jonis f+ f- (Sign.+ , n , _) p₁ = f+ p₁ refl
    jonis f+ f- (Sign.- , n , _) p₁ = f- p₁ refl

    jonais : (r : ℝ) → sign r ≡ Sign.+ ⊎ sign r ≡ Sign.-
    jonais r = jonis (λ _ → inj₁) (λ _ → inj₂) r 0
\end{code}

\subsection{\lcblm{\F{signℤ}}}

\begin{code}
  module Signℤ where
    >⇒1 : _> fromℕ 0 ⊆ (_≡ ℤ.1ℤ) ∘ signℤ
    >⇒1 = {!!}

    1⇒> : (_≡ ℤ.+_ 1) ∘ signℤ ⊆ _> fromℕ 0
    1⇒> = {!!}

    <⇒-1 : (r : ℝ) → fromℕ 0 > r → signℤ r ≡ ℤ.-[1+ 0 ]
    <⇒-1 = {!!}

    -1⇒< : (r : ℝ) → signℤ r ≡ ℤ.-[1+ 0 ] → fromℕ 0 > r
    -1⇒< = {!!}

    ≈⇒0 : (r : ℝ) → r ≈ fromℕ 0 → signℤ r ≡ ℤ.+_ 0
    ≈⇒0 = {!!}

    0⇒≈ : (r : ℝ) → signℤ r ≡ ℤ.+_ 0 → r ≈ fromℕ 0
    0⇒≈ = {!!}

    jonais : (r : ℝ)
           → let s = signℤ r ≡_ in
             s ℤ.0ℤ ⊎ s ℤ.1ℤ ⊎ s ℤ.-[1+ 0 ]
    jonais = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}>\AgdaUnderscore}}}

\begin{code}
  module _>_ where
    ≈⇒≯ : Irreflexive _≈_ _>_
    ≈⇒≯ = {!!}

    >⇒¬< : Asymmetric _>_
    >⇒¬< = {!!}

    >⇒≉ : _>_ ⇒ ¬_ ∘₂ _≈_
    >⇒≉ = {!!}

    ∃[>∧>⍨] : {r s : ℝ} → r > s → ∃ $ λ t → (r > t) × (t > s)
    ∃[>∧>⍨] {r} {s} z = frinu (r + s) (fromℕ 2) N , {!!} , {!!}
      where
      N = Fromℕ.fromℕ[s]≉0 1

    >∧>⇒> : Transitive _>_
    >∧>⇒> = {!!}

    >ℤ⇒> : (r s : ℝ) → ⌊' r ℤ.> ⌊' s → r > s
    >ℤ⇒> = {!!}

    ℕ> : ℕ._>_ ⇒ (_>_ on fromℕ)
    ℕ> = {!!}

    ℤ> : ℤ._>_ ⇒ (_>_ on fromℤ)
    ℤ> = {!!}

    ℚ> : ℚ._>_ ⇒ (_>_ on fromℚ)
    ℚ> = {!!}

    >F∧≥ℤ⇒> : (r s : ℝ)
            → ⌊'⁻¹ℝ r > ⌊'⁻¹ℝ s
            → ⌊' r ℤ.≥ ⌊' s
            → r > s
    >F∧≥ℤ⇒> = {!!}

    r<r+s : (r s : ℝ) → s > fromℕ 0 → r < (r + s)
    r<r+s = {!!}

    +r>-s : {r s : ℝ}
          → sign r ≡ Sign.+
          → sign s ≡ Sign.-
            -- | ni'o sarcu ni'i zo'e joi le su'u li no na
            -- dubmau li no
          → ¬_ $ r ≈ s
          → r > s
    +r>-s = {!!}

    jonais : (r s : ℝ) → (r > s) ⊎ (r < s) ⊎ (r ≈ s)
    jonais = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}≥\AgdaUnderscore}}}

\begin{code}
  module _≥_ where
    ≥∧≥⇒≥ : Transitive _≥_
    ≥∧≥⇒≥ = {!!}

    ≥∧≥⍨⇒≈ : Relation.Binary.Antisymmetric _≈_ _≥_
    ≥∧≥⍨⇒≈ = {!!}

    ≈⇒≥ : _≈_ ⇒ _≥_
    ≈⇒≥ = inj₁

    >⇒≥ : _>_ ⇒ _≥_
    >⇒≥ = inj₂

    r≥r : Reflexive _≥_
    r≥r = ≈⇒≥ _≈_.r≈r

    ≥⇒¬< : _≥_ ⇒ ¬_ ∘₂ _<_
    ≥⇒¬< = {!!}

    ≥∧≉⇒> : (_≥_ -×- ¬_ ∘₂ _≈_ ) ⇒ _>_
    ≥∧≉⇒> (x , N) = _⊎_.[_,_] (_⇒⇐ N) id x

    ≥∧≯⇒≈ : (_≥_ -×- ¬_ ∘₂ _>_) ⇒ _≈_
    ≥∧≯⇒≈ (x , N) = _⊎_.[_,_] id (_⇒⇐ N) x

    +r≥-s : {r s : ℝ} → sign r ≡ Sign.+ → sign s ≡ Sign.- → r ≥ s
    +r≥-s = {!!}

    ℕ≥ : ℕ._≥_ ⇒ (_≥_ on fromℕ)
    ℕ≥ = {!!}

    jonais : (r s : ℝ) → (r ≥ s) ⊎ (r < s)
    jonais r s with _>_.jonais r s
    ... | inj₁ z = inj₁ $ >⇒≥ z
    ... | inj₂ x = _⊎_.[_,_] inj₂ (inj₁ ∘ ≈⇒≥) x

    ¬≥⇒< : ¬_ ∘₂ _≥_ ⇒ _<_
    ¬≥⇒< N = _⊎_.[_,_]′ (_⇒⇐ N) id $ jonais _ _
\end{code}

\subsection{\lcblm{\F{∣\AgdaUnderscore{}∣}}}

\begin{code}
  module ∣_∣ where
    +r≡∣+r∣ : (_≡ Sign.+) ∘ sign ⊆′ (λ r → r ≡ ∣ r ∣)
    +r≡∣+r∣ _ refl = refl

    s[r]≡-⇒¯r≡∣r∣ : (_≡ Sign.-) ∘ sign ⊆′ (λ r → ¯_ r ≡ ∣ r ∣)
    s[r]≡-⇒¯r≡∣r∣ = {!!}

    0≈∣0∣ : _≈ fromℕ 0 ⊆ (λ r → r ≈ ∣ r ∣)
    0≈∣0∣ = {!!}

    r≥0⇒r≈∣r∣ : _≥ fromℕ 0 ⊆′ (λ r → r ≈ ∣ r ∣)
    r≥0⇒r≈∣r∣ r = _⊎_.[_,_] 0≈∣0∣ $ _≈_.≡⇒≈ ∘ +r≡∣+r∣ r ∘ r>0⇒s[r]≡+ r
      where
      open SignV using (r>0⇒s[r]≡+)

    0>r⇒∣r∣≈-r : fromℕ 0 >_ ⊆′ (λ r → ∣ r ∣ ≈ ¯_ r)
    0>r⇒∣r∣≈-r = {!!}

    ∣_∣≡∣_∣∘∣_∣ : Algebra.IdempotentFun _≡_ ∣_∣
    ∣_∣≡∣_∣∘∣_∣ _ = refl

    ∣_∣≈∣_∣∘∣_∣ : Algebra.IdempotentFun _≈_ ∣_∣
    ∣_∣≈∣_∣∘∣_∣ = _≈_.≡⇒≈ ∘ ∣_∣≡∣_∣∘∣_∣

    ≈⇒∣_∣≈ : Algebra.Congruent₁ _≈_ ∣_∣
    ≈⇒∣_∣≈ {r} {s} = SignV.jonis {P₁ = _≈ s} f₁ f₂ r
      where
      f₁ : {r : ℝ} → r ≈ s → sign r ≡ Sign.+ → ∣ r ∣ ≈ ∣ s ∣
      f₁ {r} d ds = SignV.jonis {P₁ = r ≈_} g₁ g₂ s d
        where
        g₁ : {s : ℝ} → r ≈ s → sign s ≡ Sign.+ → ∣ r ∣ ≈ ∣ s ∣
        g₁ {s} d dss = begin
          ∣ r ∣ ≈⟨ +r≡∣+r∣ r ds ▹ sym ▹ _≈_.≡⇒≈ ⟩
          r ≈⟨ d ⟩
          s ≈⟨ +r≡∣+r∣ s dss ▹ _≈_.≡⇒≈ ⟩
          ∣ s ∣ ∎
          where
          open import Relation.Binary.Reasoning.Setoid _≈_.setoid
        g₂ : {s : ℝ} → r ≈ s → sign s ≡ Sign.- → ∣ r ∣ ≈ ∣ s ∣
        g₂ = {!!}
      f₂ : {r : ℝ} → r ≈ s → sign r ≡ Sign.- → ∣ r ∣ ≈ ∣ s ∣
      f₂ {r} d ds = SignV.jonis {P₁ = r ≈_} g₁ g₂ s d
        where
        g₁ : {s : ℝ} → r ≈ s → sign s ≡ Sign.+ → ∣ r ∣ ≈ ∣ s ∣
        g₁ = {!!}
        g₂ : {s : ℝ} → r ≈ s → sign s ≡ Sign.- → ∣ r ∣ ≈ ∣ s ∣
        g₂ {s} d dss = begin
          ∣ r ∣ ≈⟨ s[r]≡-⇒¯r≡∣r∣ r ds ▹ sym ▹ _≈_.≡⇒≈ ⟩
          ¯ r ≈⟨ ¯_.r≈s⇒¯r≈¯s d ⟩
          ¯ s ≈⟨ s[r]≡-⇒¯r≡∣r∣ s dss ▹ _≈_.≡⇒≈ ⟩
          ∣ s ∣ ∎
          where
          open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    ∣fromℚ[k]∣≈fromℚ[∣k∣] : (k : ℚ) → ∣ fromℚ k ∣ ≈ fromℚ ℚ.∣ k ∣
    ∣fromℚ[k]∣≈fromℚ[∣k∣] k@(ℚ.mkℚ (ℤ.pos m) n c) = begin
      ∣ fromℚ k ∣ ≈⟨ _≈_.r≈r ⟩
      ∣ fromℚ $ ℚ.mkℚ (ℤ.pos m) n c ∣ ≈⟨ _≈_.r≈r ⟩
      ∣ frinu (fromℤ $ ℤ.+ m) (fromℕ $ ℕ.suc n) N ∣ ≈⟨ {!!} ⟩
      fromℚ ℚ.∣ k ∣ ∎
      where
      N = Fromℕ.fromℕ[s]≉0 _ 
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
    ∣fromℚ[k]∣≈fromℚ[∣k∣] (ℚ.mkℚ (ℤ.negsuc m) n c) = {!!}

    jonais : (r : ℝ) → (∣ r ∣ ≈ r) ⊎ (∣ r ∣ ≈ ¯_ r)
    jonais r with _≥_.jonais r $ fromℕ 0
    ... | inj₁ djm = inj₁ $ _≈_.≈⇒≈⍨ $ r≥0⇒r≈∣r∣ _ djm
    ... | inj₂ m = inj₂ $ 0>r⇒∣r∣≈-r _ m

    R[∣R∣] : (r : ℝ) → Rational r → Rational ∣ r ∣
    R[∣R∣] r (r' , d) = _,_ ℚ.∣ r' ∣ $ _≈_.≈⇒≈⍨ $ begin
      fromℚ ℚ.∣ r' ∣ ≈⟨ ∣fromℚ[k]∣≈fromℚ[∣k∣] r' ▹ _≈_.≈⇒≈⍨ ⟩
      ∣ fromℚ r' ∣ ≈⟨ ≈⇒∣_∣≈ d ▹ _≈_.≈⇒≈⍨ ⟩
      ∣ r ∣ ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid

    R[∣r∣]⇒R[r] : (r : ℝ) → Rational ∣ r ∣ → Rational r
    R[∣r∣]⇒R[r] = SignV.jonis f₁ f₂
      where
      f₁ : {r : ℝ} → Rational ∣ r ∣ → sign r ≡ Sign.+ → Rational r
      f₁ R d = subst Rational (sym $ +r≡∣+r∣ _ d) R
      f₂ : {r : ℝ} → Rational ∣ r ∣ → sign r ≡ Sign.- → Rational r
      f₂ R d = subst Rational (¯∣¯r∣≡r _ d) $ ¯_.R[¯R] R
        where
        ¯∣¯r∣≡r : (r : ℝ) → sign r ≡ Sign.- → ¯_ ∣ r ∣ ≡ r
        ¯∣¯r∣≡r r d = begin
          ¯ ∣ r ∣ ≡⟨ s[r]≡-⇒¯r≡∣r∣ r d ▹ sym ▹ cong ¯_ ⟩
          ¯ (¯ r) ≡⟨ ¯_.r≡¯¯r r ▹ sym ⟩
          r ∎
          where
          open import Relation.Binary.PropositionalEquality
          open ≡-Reasoning

    I[∣I∣] : Irrational ⊆ Irrational ∘ ∣_∣
    I[∣I∣] = jonis f₁ f₂ _
      where
      jonis = SignV.jonis {P₁ = Irrational} {P₂ = Irrational ∘ ∣_∣}
      f₁ : {r : ℝ} → Irrational r → sign r ≡ Sign.+ → Irrational ∣ r ∣
      f₁ I d = subst Irrational (+r≡∣+r∣ _ d) I
      f₂ : {r : ℝ} → Irrational r → sign r ≡ Sign.- → Irrational ∣ r ∣
      f₂ I d = subst Irrational {!!} $ ¯_.I[¯I] _ I

    I[∣r∣]⇒I[r] : Irrational ∘ ∣_∣ ⊆′ Irrational
    I[∣r∣]⇒I[r] = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}⊓\AgdaUnderscore}}}

\begin{code}
  module _⊓_ where
    module I where
      open _⊓_I
        using (
          _≥ᵇ_;
          bool'
        )

      ≥⇒⊤ : _≥_ ⇒ _≡_ true ∘₂ _≥ᵇ_
      ≥⇒⊤ = {!!}

      ⊤⇒≥ : _≡_ true ∘₂ _≥ᵇ_ ⇒ _≥_
      ⊤⇒≥ = {!!}

      <⇒⊥ : (r s : ℝ) → r < s → false ≡ r ≥ᵇ s
      <⇒⊥ = {!!}

      ⊥⇒≤ : (r s : ℝ) → false ≡ r ≥ᵇ s → r ≤ s
      ⊥⇒≤ r s d = _≥_.jonais s r ▹ _⊎_.[_,_]′ id f
        where
        T⇒¬F : _≡_ true ⊆ ¬_ ∘ _≡_ false
        T⇒¬F refl ()
        f = d ⇒⇐_ ∘′ T⇒¬F ∘′ ≥⇒⊤ {r} {s} ∘′ _≥_.>⇒≥

      ⊥⇒1 : ∀ {a} → {A : Set a} → (x z : A) → x ≡ bool' x z false
      ⊥⇒1 _ _ = refl

      ⊤⇒2 : ∀ {a} → {A : Set a}
          → (x : A)
          → {z : A}
          → z ≡ bool' x z true
      ⊤⇒2 _ = refl

    -- | ni'o xu zmadu fa tu'a zoi zoi. r<s⇒r≡r⊓s .zoi...
    -- fi zo'e ji le ka ce'u mabla barda
    <⇒1 : (r s : ℝ) → r < s → r ≡ r ⊓ s
    <⇒1 r s m = subst (_≡_ r ∘ _⊓_I.bool' r s) (I.<⇒⊥ r s m) 1'
      where
      1' = I.⊥⇒1 r s

    ≥⇒2 : _≥_ ⇒ (λ r s → s ≡ r ⊓ s)
    ≥⇒2 {r} {s} z = subst (_≡_ s ∘ _⊓_I.bool' r s) (I.≥⇒⊤ z) (I.⊤⇒2 r)

    ≈⇒1 : _≈_ ⇒ (λ r s → r ≈ (r ⊓ s))
    ≈⇒1 = _≈_.≈∧≈⇒≈ ˢ _≈_.≡⇒≈ ∘ ≥⇒2 ∘ _≥_.≈⇒≥

    ≈⇒2 : _≈_ ⇒ (λ r s → s ≈ (r ⊓ s))
    ≈⇒2 = _≈_.≡⇒≈ ∘ ≥⇒2 ∘ _≥_.≈⇒≥

    r⊓s≈r'⊓s' : Algebra.Congruent₂ _≈_ _⊓_
    r⊓s≈r'⊓s' = {!!}

    ⊓≈⊓⍨ : Commutative _≈_ _⊓_
    ⊓≈⊓⍨ r s with _≥_.jonais r s
    ... | inj₁ djm = begin
      r ⊓ s ≈⟨ ≥⇒2 djm ▹ sym ▹ _≈_.≡⇒≈ ⟩
      s ≈⟨ ≤⇒1 s r djm ⟩
      s ⊓ r ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      ≤⇒1 : (r s : ℝ) → r ≤ s → r ≈ (r ⊓ s)
      ≤⇒1 r s = _⊎_.[_,_] (≈⇒1 ∘ _≈_.≈⇒≈⍨) $ _≈_.≡⇒≈ ∘ <⇒1 r s
    ... | inj₂ m = _≈_.≡⇒≈ $ begin
      r ⊓ s ≡⟨ <⇒1 r s m ▹ sym ⟩
      r ≡⟨ ≥⇒2 {s} $ _≥_.>⇒≥ m ⟩
      s ⊓ r ∎
      where
      open ≡-Reasoning

    ⊓-ass : Associative _≈_ _⊓_
    ⊓-ass r s t with _≥_.jonais r s ,′ _≥_.jonais s t
    ... | (inj₁ djm₁ , inj₁ djm₂) = _≈_.≡⇒≈ $ begin
      (r ⊓ s) ⊓ t ≡⟨ ≥⇒2 djm₁ ▹ sym ▹ cong (_⊓ t) ⟩
      s ⊓ t ≡⟨ ≥⇒2 $ _≥_.≥∧≥⇒≥ djm₁ djm₂' ⟩
      r ⊓ (s ⊓ t) ∎
      where
      open ≡-Reasoning
      djm₂' = subst (_ ≥_) (≥⇒2 djm₂) djm₂
      open import Relation.Binary.PropositionalEquality
    ... | (inj₁ djm₁ , inj₂ m₂) = {!!}
    ... | (inj₂ m₁ , inj₁ djm₂) = {!!}
    ... | (inj₂ m₁ , inj₂ m₂) = begin
      (r ⊓ s) ⊓ t ≈⟨ <⇒1 r s m₁ ▹ sym ▹ cong (_⊓ t) ▹ _≈_.≡⇒≈ ⟩
      r ⊓ t ≈⟨ {!!} ▹ r⊓s≈r'⊓s' {r} {u = t} {s ⊓ t} _≈_.r≈r ⟩
      r ⊓ (s ⊓ t) ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
      cong = Relation.Binary.PropositionalEquality.cong

    ⊓-sel : Algebra.Selective _≡_ _⊓_
    ⊓-sel r s with _≥_.jonais r s
    ... | x = _⊎_.[_,_]′ (inj₂ ∘ sym ∘ ≥⇒2) (inj₁ ∘ sym ∘ <⇒1 _ s) x

    id≈⊓⍨ : Algebra.Idempotent _≈_ _⊓_
    id≈⊓⍨ _ = _≈_.≈⇒≈⍨ $ ≈⇒1 _≈_.r≈r
\end{code}

\subsection{\lcblm{\F{fromℚ}}}

\begin{code}
  module Fromℚ where
    fromℚ-Rational : (k : ℚ) → Rational $ fromℚ k
    fromℚ-Rational = _, _≈_.r≈r

    id≡_∘fromℚ : id ≗ proj₁ ∘ fromℚ-Rational
    id≡_∘fromℚ _ = refl
\end{code}

\subsection{\lcblm{\F{Irrational}}}

\begin{code}
  module Irrational where
    I[r]∧r≈s⇒I[s] : {r s : ℝ} → Irrational r → r ≈ s → Irrational s
    I[r]∧r≈s⇒I[s] = _+_.VI.I[r]∧r≈s⇒I[s]

    R⊎I : (r : ℝ) → Rational r ⊎ Irrational r
    R⊎I = {!!}
\end{code}

\subsection{\lcblm{\F{toℚ}}}

\begin{code}
  module Toℚ where
    id≡toℚ∘fromℚ : id ≗ (λ k → toℚ {fromℚ k} $ Fromℚ.fromℚ-Rational k)
    id≡toℚ∘fromℚ _ = refl

    toℚ∘fromℕ : toℚ ∘ Fromℕ.fromℕ-Rational ≗ (ℚ.fromℤ ∘ ℤ.+_)
    toℚ∘fromℕ _ = refl

    toℚ∘fromℤ : toℚ ∘ Fromℤ.fromℤ-Rational ≗ ℚ.fromℤ
    toℚ∘fromℤ z = begin
      toℚ (Fromℤ.fromℤ-Rational z) ≡⟨ refl ⟩
      proj₁ (Fromℤ.fromℤ-Rational z) ≡⟨ refl ⟩
      ℚ.mkℚ z 0 _ ∎
      where
      open ≡-Reasoning
\end{code}

\section{le ctaipe be le su'u sumji joi co'e me'oi .group.}

\begin{code}
+--group : Algebra.IsGroup _≈_ _+_ (fromℕ 0) (fromℕ 0 -_)
+--group = record {
  isMonoid = record {
    isSemigroup = {!!};
    identity = Veritas._+_.id≈+0};
  inverse = {!!};
  ⁻¹-cong = {!!}}
\end{code}

\section{le ctaipe be le su'u sumji mu'oi glibau.\ abelian group .glibau.}

\begin{code}
ga+ : Algebra.IsAbelianGroup _≈_ _+_ (fromℕ 0) $ fromℕ 0 -_
ga+ = record {isGroup = +--group; comm = Veritas._+_.+≈+⍨}
\end{code}

\section{le ctaipe be le su'u me'oi .ring.}

\begin{code}
isRing : IsRing _≈_ _+_ _*_ (fromℕ 0 -_) (fromℕ 0) (fromℕ 1)
isRing = record {
  +-isAbelianGroup = ga+;
  *-isMonoid = record {
    isSemigroup = record {
      isMagma = Veritas._*_.*-magma;
      assoc = Veritas._*_.*-ass};
    identity = Veritas._*_.r≈1*r};
  distrib = Veritas._*_.dist;
  zero = Veritas._*_.0≈0*r}
\end{code}
\end{document}
