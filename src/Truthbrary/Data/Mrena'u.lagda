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
\newunicodechar{⟪}{\ensuremath{\mathnormal{\langle\hspace{-0.2em}\langle}}}
\newunicodechar{⟫}{\ensuremath{\mathnormal{\rangle\hspace{-0.2em}\rangle}}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{¯}{\ensuremath{\mathnormal{^{-}}}}
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

open import Level
  using (
  )
open import Algebra
  using (
    LeftIdentity;
    Associative;
    Commutative;
    IsRing;
    Zero;
    Op₂
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
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    _-⟪_⟫-_;
    const;
    _∘₂_;
    _∘_;
    _$_
  )
  renaming (
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
    Irreflexive;
    Asymmetric;
    Transitive;
    Reflexive;
    Setoid
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Data.Fin.Patterns
  using (
    9F
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
\end{code}

\section{la'oi .\F ℝ.}
ni'o ro da zo'u da mrena'u jo cu ctaipe la'oi .\F ℝ.  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B s \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore{}}\B a \B b\Sym)\ .zoi.\ poi ke'a ctaipe la'oi .\F ℝ.\ cu pilji lo sumji be la'oi .\B a.\ bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.\ zo'e poi ga jonai ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.+}\ .zoi.\ gi ke'a du li pa gi ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.-}\ .zoi.\ gi ke'a du li ni'u pa  .i ga jo la'oi .\F ℝ.\ se ctaipe ko'a goi la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \AgdaUnderscore{} \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore} \AgdaUnderscore\ \B f\Sym)\ .zoi.\ gi la'o zoi.\ \B f \B n\ .zoi.\ meirmoi la'oi .\B n.\ fo lo me'oi .digit.\ be lo cmalu pagbu be lo mu'oi glibau.\ decimal expansion .glibau.\ be ko'a

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
  ⊎/ = 𝕃.foldr _-⟪ _⊎_ ⟫-_ $ λ _ _ → ⊥
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
_≥_ r s = (r ≈ s) ⊎ (r > s)
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≤\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≤ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavme'a la'oi .\B b.

\begin{code}
_≤_ : ℝ → ℝ → Set
_≤_ = _≥_ ⍨
\end{code}

\section{la'o zoi.\ \F{⌊'}\ .zoi.}
ni'o du la'oi .\B r.\ fa lo sumji be la'o zoi.\ \F{⌊'} \B r\ .zoi.\ be lo co'e be la'o zoi.\ \AgdaField{proj₂} \OpF \$ \AgdaField{proj₂} \B r\ .zoi.

\begin{code}
⌊' : ℝ → ℤ
⌊' (Sign.+ , n , _) = ℤ.+ n
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
ni'o ro da poi ke'a ctaipe la'oi .\F ℝ.\ zo'u ga jonai ga je da zmadu li no gi du la'o zoi.\ \IC{Sign.+}\ .zoi.\ fa ko'a goi lo me'oi .\F{sign}.\ be da gi ko'a du la'o zoi.\ \IC{Sign.-}\ .zoi.

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
ni'o la'o zoi.\ \AgdaOperator{¯} \B r\ .zoi.\ vujnu li no la'oi .\B r.

\begin{code}
¯_ : ℝ → ℝ
¯_ (Sign.+ , n , f) = Sign.- , n , f
¯_ (Sign.- , n , f) = Sign.+ , n , f
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
fromℤ (ℤ.pos n) = fromℕ n
fromℤ (ℤ.negsuc n) = ¯ fromℕ n
\end{code}

\section{la'o zoi.\ \F{from𝔻}\ .zoi.}
ni'o la .varik.\ na birti lo du'u ma kau zabna je cu lojbo je cu velcki la'o zoi.\ \F{from𝔻}\ .zoi.  .i ku'i lakne fa lo nu la .varik.\ cu facki

\begin{code}
from𝔻 : Sign → (ℕ → Digit 10) → ℝ
from𝔻 s f = fromℝ- s 0 f
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
_-_ r s = r + (¯ s)
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
  fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
  fromℕ[s]≉0 = N ∘₂ r≈0⇒⌊'r≡0 ∘ fromℕ ∘ ℕ.suc
    where
    N : {n : ℕ} → ¬_ $ ⌊' (fromℕ $ ℕ.suc n) ≡ ℤ.+ 0
    N ()
    r≈0⇒⌊'r≡0 : (r : ℝ) → r ≈ fromℕ 0 → ⌊' r ≡ ℤ.+ 0
    r≈0⇒⌊'r≡0 = {!!}

fromℚ : ℚ → ℝ
fromℚ (ℚ.mkℚ a b N) = frinu (fromℤ a) 1+b $ fromℕ[s]≉0 b
  where
  open FromℚI
  1+b = fromℕ $ ℕ.suc b
\end{code}

\section{la'oi .\F{Rational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Rational} \B r\ .zoi.\ gi la'oi .\B r.\ me'oi .rational.  .i cadga fa lo nu li'armi  .i le velcki zo'u ro da poi ke'a co'e zo'u da me'oi .rational.\ jo cu du lo su'o frinu

\begin{code}
Rational : ℝ → Set
Rational r = ∃ $ r ≈_ ∘ fromℚ
\end{code}

\section{la'oi .\F{Irrational}.}
ni'o ga jo ctaipe la'o zoi.\ \F{Irrational} \B r\ .zoi.\ gi la'oi .\B r.\ me'oi .irrational.  .i cadga fa lo nu li'armi  .i le velcki zo'u ro da poi ke'a co'e zo'u da me'oi .irrational.\ jo cu du lo no frinu

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
  f : ∀ {a} → {A : Set a} → A → A → Bool → A
  f r s n = if n then s else r

  _≥ᵇ_ : ℝ → ℝ → Bool
  _≥ᵇ_ = {!!}

_⊓_ : ℝ → ℝ → ℝ
_⊓_ r s = f r s $ _≥ᵇ_ r s
  where
  open _⊓_I
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}⊔\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B r \OpF ⊔ \B s\ .zoi.\ nacyzmarai la'oi .\B r.\ ce la'oi .\B s.

\begin{code}
_⊔_ : ℝ → ℝ → ℝ
_⊔_ r s = _⊓_I.f s r $ _⊓_I._≥ᵇ_ r s
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

    ≡⇒≈ : {r s : ℝ} → r ≡ s → r ≈ s
    ≡⇒≈ refl = ≡∧≗⇒≈ refl $ λ _ → refl

    r≈r : (r : ℝ) → r ≈ r
    r≈r _ = ≡⇒≈ refl

    ≈⇒≈⍨ : {r s : ℝ} → r ≈ s → s ≈ r
    ≈⇒≈⍨ = {!!}

    ≈⇒≯ : {r s : ℝ} → r ≈ s → ¬_ $ r > s
    ≈⇒≯ = {!!}

    id≡[≈⇒≈⍨]² : (r s : ℝ)
               → (d : r ≈ s)
               → d ≡_ $ ≈⇒≈⍨ $ ≈⇒≈⍨ d
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
       → ¬_ $ ⌊'⁻¹ r i ≡ 9F
       → 𝔽.toℕ (⌊'⁻¹ s i) ≡ ℕ.suc (𝔽.toℕ $ ⌊'⁻¹ r i)
       → (_ : (i' : 𝔽.Fin $ i ℕ.+ 1)
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

    ∣r-s∣>0⇒r≉s : (r s : ℝ)
                → ∣ r - s ∣ > fromℕ 0
                → ¬_ $ r ≈ s
    ∣r-s∣>0⇒r≉s = {!!}

    r≉s⇒∣r-s∣>0 : (r s : ℝ)
                → ¬_ $ r ≈ s
                → ∣ r - s ∣ > fromℕ 0
    r≉s⇒∣r-s∣>0 = {!!}

    r≈s⇒∣r-s∣≈0 : (r s : ℝ)
                → r ≈ s
                → ∣ r - s ∣ ≈ fromℕ 0
    r≈s⇒∣r-s∣≈0 = {!!}

    ∣r-s∣≈0⇒r≈s : (r s : ℝ)
                → ∣ r - s ∣ ≈ fromℕ 0
                → r ≈ s
    ∣r-s∣≈0⇒r≈s = {!!}

    ¬[r≈s⇒fr≈fs] : ¬ ((r s : ℝ) → (f : ℝ → ℝ) → r ≈ s → f r ≈ f s)
    ¬[r≈s⇒fr≈fs] = {!!}

    isEquivalence : Relation.Binary.IsEquivalence _≈_
    isEquivalence = record {
      refl = r≈r _;
      sym = ≈⇒≈⍨;
      trans = ≈∧≈⇒≈}

    setoid : Setoid _ _
    setoid = record {_≈_ = _≈_; isEquivalence = isEquivalence}

    0≈-0 : fromℕ 0 ≈ (¯ fromℕ 0)
    0≈-0 = {!!}
\end{code}

\subsection{\lcblm{\F{fromℕ}}}

\begin{code}
  module Fromℕ where
    pav : (n : ℕ) → ℤ.+_ n ≡ ⌊' (fromℕ n)
    pav _ = refl

    rel : (m n : ℕ) → 𝔽.zero ≡ ⌊'⁻¹ (fromℕ m) n
    rel _ _ = refl

    ≢⇒≉ : (m n : ℕ) → ¬_ $ m ≡ n → ¬_ $ fromℕ m ≈ fromℕ n
    ≢⇒≉ = {!!}

    fromℕ[s]≉0 : (n : ℕ) → ¬_ $ fromℕ (ℕ.suc n) ≈ fromℕ 0
    fromℕ[s]≉0 = FromℚI.fromℕ[s]≉0

    fromℕ-fromℚ : (n : ℕ)
                → let C = Coprime.sym $ Coprime.1-coprimeTo n in
                  fromℕ n ≈ fromℚ (ℚ.mkℚ (ℤ.+_ n) 0 C)
    fromℕ-fromℚ = {!!}

    fromℕ-Rational : (n : ℕ) → Rational $ fromℕ n
    fromℕ-Rational n = ℚ.mkℚ (ℤ.+_ n) 0 c , fromℕ-fromℚ n
      where
      c = Coprime.sym $ 1-coprimeTo _

    id≡∣_∣∘⌊'∘fromℕ : (n : ℕ) → n ≡ ℤ.∣ ⌊' $ fromℕ n ∣
    id≡∣_∣∘⌊'∘fromℕ _ = refl

    fromℕ≥0 : (n : ℕ) → fromℕ n ≥ fromℕ 0
    fromℕ≥0 0 = inj₁ $ _≈_.≡⇒≈ refl
    fromℕ≥0 (ℕ.suc n) = inj₂ {!!}
\end{code}

\subsection{\lcblm{\F{fromℤ}}}

\begin{code}
  module Fromℤ where
    fromℤ-Rational : (z : ℤ) → Rational $ fromℤ z
    fromℤ-Rational z = ℤ→ℚ z , fromℤ≈fromℚ∘ℤ→ℚ z
      where
      ℤ→ℚ : ℤ → ℚ
      ℤ→ℚ z = ℚ.mkℚ z 0 (Coprime.sym $ 1-coprimeTo _)
      fromℤ≈fromℚ∘ℤ→ℚ : (z : ℤ) → fromℤ z ≈ fromℚ (ℤ→ℚ z)
      fromℤ≈fromℚ∘ℤ→ℚ = λ z → _≈_.≈⇒≈⍨ $ begin
        fromℚ (ℤ→ℚ z) ≈⟨ _≈_.r≈r _ ⟩
        fromℚ (ℚ.mkℚ z 0 (Coprime.sym $ 1-coprimeTo _)) ≈⟨ _≈_.r≈r _ ⟩
        frinu (fromℤ z) (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0) ≈⟨ _≈_.r≈r _ ⟩
        _ ≈⟨ _≈_.≡⇒≈ $ sym $ r≡r/1 $ fromℤ z ⟩
        fromℤ z ∎
        where
        open import Relation.Binary.Reasoning.Setoid _≈_.setoid
        r≡r/1 : (r : ℝ) → r ≡ frinu r (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0)
        r≡r/1 = {!!}
\end{code}

\subsection{\lcblm{\F{¯\AgdaUnderscore}}}

\begin{code}
  module ¯_ where
    r≈-r⇒r≈0 : (r : ℝ)
             → r ≈_ $ ¯ r
             → r ≈ fromℕ 0
    r≈-r⇒r≈0 = {!!}

    r>0⇒¯r≈¯r : (r : ℝ)
              → r > fromℕ 0
              → (¯ r) ≈ fromℝ- Sign.- ℤ.∣ ⌊' r ∣ (⌊'⁻¹ r)
    r>0⇒¯r≈¯r = {!!}

    r<0⇒¯r≈∣r∣ : (r : ℝ) → fromℕ 0 > r → (¯ r) ≈ ∣ r ∣
    r<0⇒¯r≈∣r∣ = {!!}

    r-¯s≈r+s : (r s : ℝ) → (r - (¯ s)) ≈ (r + s)
    r-¯s≈r+s = {!!}

    R[¯R] : (r : ℝ) → Rational r → Rational $ ¯ r
    R[¯R] = {!!}

    I[¯I] : (r : ℝ) → Irrational r → Irrational $ ¯ r
    I[¯I] = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}+\AgdaUnderscore}}}

\begin{code}
  module _+_ where
    +≈+⍨ : Commutative _≈_ _+_
    +≈+⍨ = {!!}

    +-ass : Associative _≈_ _+_
    +-ass = {!!}

    id≡+0 : Algebra.Identity _≡_ (fromℕ 0) _+_
    id≡+0 = {!!} , {!!}

    id≈+0 : Algebra.Identity _≈_ (fromℕ 0) _+_
    id≈+0 = {!!}

    dratadratas : (r s : ℝ)
                → ¬_ $ r ≈ fromℕ 0 × s ≈ fromℕ 0
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

    r≡f+z : (s : Sign)
          → (n : ℕ)
          → (f : ℕ → Digit 10)
          → (_≡_
              (fromℝ- s n f)
              (from𝔻 s f + fromℤ (s ℤ.◃ n)))
    r≡f+z = {!!}

    ℕ+ : (m n : ℕ) → fromℕ m + fromℕ n ≡ fromℕ (m ℕ.+ n)
    ℕ+ = {!!}

    ℤ+ : (x z : ℤ) → fromℤ x + fromℤ z ≡ fromℤ (x ℤ.+ z)
    ℤ+ = {!!}

    ℚ+ : {r s : ℝ}
       → (r' : Rational r)
       → (s' : Rational s)
       → r + s ≡ fromℚ (proj₁ r' ℚ.+ proj₁ s')
    ℚ+ = {!!}

    r≉r+s : (r s : ℝ) → ¬_ $ s ≈ fromℕ 0 → ¬_ $ r ≈_ $ r + s
    r≉r+s = {!!}

    R[R+R] : (r s : ℝ) → Rational r → Rational s → Rational $ r + s
    R[R+R] r s R@(r' , _) S@(s' , _) = r' ℚ.+ s' , _≈_.≡⇒≈ D
      where
      D = ℚ+ R S

    I[I+R] : (r s : ℝ) → Irrational r → Rational s → Irrational $ r + s
    I[I+R] = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}-\AgdaUnderscore}}}

\begin{code}
  module _-_ where
    0≈r-s : (r s : ℝ) → r ≈ s → fromℕ 0 ≈_ $ r - s
    0≈r-s = {!!}

    0≈r-r : (r : ℝ) → fromℕ 0 ≈_ $ r - r
    0≈r-r r = 0≈r-s r r $ _≈_.≡⇒≈ refl

    0≡r-0 : Algebra.RightZero _≡_ (fromℕ 0) _-_
    0≡r-0 = {!!}

    r-s-t≈r-[s+t] : (r s t : ℝ) → ((r - s) - t) ≈ (r - (s + t))
    r-s-t≈r-[s+t] = {!!}

    -r≈0-r : (r : ℝ) → (¯ r) ≈ (fromℕ 0 - r)
    -r≈0-r = {!!}

    r≈[r-s]+s : (r s : ℝ) → r ≈_ $ (r - s) + s
    r≈[r-s]+s = {!!}

    r≈0-[0-r] : (r : ℝ) → r ≈_ $ fromℕ 0 -_ $ fromℕ 0 - r
    r≈0-[0-r] = {!!}

    0≈r+[0-r] : (r 0' : ℝ)
              → 0' ≈ fromℕ 0
              → fromℕ 0 ≈_ $ r + (0' - r)
    0≈r+[0-r] = {!!}

    r>r-s : (r s : ℝ) → s > fromℕ 0 → r >_ $ r - s
    r>r-s = {!!}

    I[I-R] : (r s : ℝ) → Irrational r → Rational s → Irrational $ r - s
    I[I-R] = {!!}

    R[R-R] : (r s : ℝ) → Rational r → Rational s → Rational $ r - s
    R[R-R] r s R S = _+_.R[R+R] r (¯ s) R {!!}
\end{code}

\subsection{\lcblm{\F{from𝔻}}}

\begin{code}
  module From𝔻 where
    S≡S : (s : Sign) → (f : ℕ → Digit 10) → s ≡ sign (from𝔻 s f)
    S≡S _ _ = refl

    f≡f : (s : Sign)
        → (f : ℕ → Digit 10)
        → f ≗ ⌊'⁻¹ (from𝔻 s f)
    f≡f = {!!}

    0≡⌊'[from𝔻] : (s : Sign)
                → (f : ℕ → Digit 10)
                → ℤ.+_ 0 ≡ ⌊' (from𝔻 s f)
    0≡⌊'[from𝔻] Sign.+ _ = refl
    0≡⌊'[from𝔻] Sign.- _ = refl

    id≡⌊'⁻¹∘from𝔻x : (s : Sign)
                   → (f : ℕ → Digit 10)
                   → f ≡ ⌊'⁻¹ (from𝔻 s f)
    id≡⌊'⁻¹∘from𝔻x = λ _ _ → refl
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
                (from𝔻 (sign r) {!!})
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
                   (signℤ r ℤ.*_ $ ℤ.+_ $ 𝔽.toℕ $ ⌊'⁻¹ r 0))))
    r*10≈_ = {!!}

    r*s>r : (r s : ℝ)
          → r > fromℕ 0
          → s > fromℕ 1
          → (r * s) > r
    r*s>r = {!!}

    r>r*s : (r s : ℝ)
          → r > fromℕ 0
          → fromℕ 1 > ∣_∣ s
          → r >_ $ r * s
    r>r*s = {!!}

    I[I*R] : (r s : ℝ) → Irrational r → Rational s → Irrational $ r * s
    I[I*R] = {!!}

    R[R*R] : (r s : ℝ) → Rational r → Rational s → Rational $ r * s
    R[R*R] = {!!}

    a*b≈a'*b' : (a a' b b' : ℝ)
              → a ≈ a'
              → b ≈ b'
              → (a * b) ≈ (a' * b')
    a*b≈a'*b' = {!!}

    *-magma : Algebra.IsMagma _≈_ _*_
    *-magma = record {
      isEquivalence = _≈_.isEquivalence;
      ∙-cong = a*b≈a'*b' _ _ _ _}
\end{code}

\subsection{\lcblm{\F{frinu}}}

\begin{code}
  module Frinu where
    module I where
      r>1⇒r≉0 : (r : ℝ) → r > fromℕ 1 → ¬_ $ r ≈ fromℕ 0
      r>1⇒r≉0 r = >⇒≉ r _ ∘ r>1⇒r>0 {r}
        where
        >⇒≉ : (r s : ℝ) → r > s → ¬_ $ r ≈ s
        >⇒≉ = {!!}
        r>1⇒r>0 : {r : ℝ} → r > fromℕ 1 → r > fromℕ 0
        r>1⇒r>0 = {!!}

    sez≡1 : (r : ℝ) → (N : _) → frinu r r N ≡ fromℕ 1
    sez≡1 = {!!}

    r≡r/1 : (r : ℝ) → r ≡ frinu r (fromℕ 1) (Fromℕ.fromℕ[s]≉0 0)
    r≡r/1 = {!!}

    0≈0/r : (r s : ℝ)
          → (N : _)
          → s ≈ fromℕ 0
          → fromℕ 0 ≈ frinu s r N
    0≈0/r = {!!}

    ∣r/s∣<∣r∣ : (r s : ℝ)
              → ¬_ $ s ≈ fromℕ 0
              → (z : s > fromℕ 1)
              → ∣ r ∣ > ∣ frinu r s (I.r>1⇒r≉0 s z) ∣
    ∣r/s∣<∣r∣ = {!!}

    ∣r/s∣≤∣r∣ : (r s : ℝ)
              → (z : s > fromℕ 1)
              → ∣ r ∣ ≥ ∣ frinu r s (I.r>1⇒r≉0 s z) ∣
    ∣r/s∣≤∣r∣ = {!!}

    -r/-s<-r : (r s : ℝ)
             → (z : s > fromℕ 1)
             → let -_ = _-_ $ fromℕ 0 in
               (- r) > frinu (- r) (- s) {!!}
    -r/-s<-r = {!!}

    r<r/s : (r s : ℝ)
          → (N : _)
          → fromℕ 1 > s
          → s > fromℕ 0
          → r > frinu r s N
    r<r/s = {!!}

    r≈s*r/s : (r s : ℝ)
            → (N : _)
            → r ≈_ $ s * frinu r s N
    r≈s*r/s = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}\textasciicircum\AgdaUnderscore}}}

\begin{code}
  module _^_ where
    id≡_^1 : Algebra.RightIdentity _≡_ (fromℕ 1) _^_
    id≡_^1 = {!!}

    1≡1^r : (r : ℝ) → fromℕ 1 ≡ fromℕ 1 ^ r
    1≡1^r = {!!}

    1≡r^0 : (r 0' : ℝ) → 0' ≈ fromℕ 0 → fromℕ 1 ≡ r ^ 0'
    1≡r^0 = {!!}

    0≈0^r : (r s : ℝ)
          → ¬_ $ r ≈ fromℕ 0
          → s ≈ fromℕ 0
          → fromℕ 0 ≈_ $ s ^ r
    0≈0^r = {!!}

    1≡0^0 : fromℕ 1 ≡ fromℕ 0 ^ fromℕ 0
    1≡0^0 = 1≡r^0 0' 0' $ _≈_.≡⇒≈ refl
      where
      0' = fromℕ 0

    [r^s]^t≈r^[s*t] : (r s t : ℝ) → ((r ^ s) ^ t) ≈ (r ^ (s * t))
    [r^s]^t≈r^[s*t] = {!!}

    r≈[r^s]^[1/s] : (r s : ℝ)
                  → (N : _)
                  → r ≈_ $ (r ^ s) ^ frinu (fromℕ 1) s N
    r≈[r^s]^[1/s] = {!!}

    R[R^ℕ] : (r : ℝ)
           → (n : ℕ)
           → Rational r
           → Rational $ r ^ fromℕ n
    R[R^ℕ] = {!!}

    R[R^r] : (r s : ℝ)
           → Set Function.∋ {!!}
           → Rational r → Rational $ r ^ s
    R[R^r] = {!!}
    
    I[2^[1/2]] : (Irrational $ _^_
                   (fromℕ 2)
                   (frinu (fromℕ 1) _ (Fromℕ.≢⇒≉ 2 0 $ λ ())))
    I[2^[1/2]] = {!!}
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

    ∃f≡ : (r : ℝ) → ∃ $ _≡_ r ∘ _+ fromℤ (⌊' r)
    ∃f≡ r = ⌊'⁻¹ℝ r , _+_.r≡r₂+r₁ r
\end{code}

\subsection{\lcblm{\F{⌊'⁻¹ℝ}}}

\begin{code}
  module ⌊'⁻¹ℝ where
    I⇒I[⌊'⁻¹ℝ] : (r : ℝ) → Irrational r → Irrational $ ⌊'⁻¹ℝ r
    I⇒I[⌊'⁻¹ℝ] = {!!}

    I[⌊'⁻¹ℝ]⇒I : (r : ℝ) → Irrational $ ⌊'⁻¹ℝ r → Irrational r
    I[⌊'⁻¹ℝ]⇒I = {!!}

    ⌊'⁻¹ℝ≡⌊'⁻¹ℝ∘⌊'⁻¹ℝ : Algebra.IdempotentFun _≡_ ⌊'⁻¹ℝ
    ⌊'⁻¹ℝ≡⌊'⁻¹ℝ∘⌊'⁻¹ℝ _ = refl

    from𝔻≡⌊'⁻¹ℝ∘from𝔻 : (s : Sign)
                      → (f : ℕ → Digit 10)
                      → from𝔻 s f ≡ ⌊'⁻¹ℝ (from𝔻 s f)
    from𝔻≡⌊'⁻¹ℝ∘from𝔻 _ _ = refl
\end{code}

\subsection{\lcblm{\F{sign}}}

\begin{code}
  module SignV where
    r>0⇒s[r]≡+ : (r : ℝ) → r > fromℕ 0 → sign r ≡ Sign.+
    r>0⇒s[r]≡+ = {!!}

    r<0⇒s[r]≡- : (r : ℝ) → r < fromℕ 0 → sign r ≡ Sign.-
    r<0⇒s[r]≡- = {!!}
\end{code}

\subsection{\lcblm{\F{signℤ}}}

\begin{code}
  module Signℤ where
    >⇒1 : (r : ℝ) → r > fromℕ 0 → signℤ r ≡ ℤ.+_ 1
    >⇒1 = {!!}

    1⇒> : (r : ℝ) → signℤ r ≡ ℤ.+_ 1 → r > fromℕ 0
    1⇒> = {!!}

    <⇒-1 : (r : ℝ) → fromℕ 0 > r → signℤ r ≡ ℤ.-_ (ℤ.+_ 1)
    <⇒-1 = {!!}

    -1⇒< : (r : ℝ) → signℤ r ≡ ℤ.-_ (ℤ.+_ 1) → fromℕ 0 > r
    -1⇒< = {!!}

    ≈⇒0 : (r : ℝ) → r ≈ fromℕ 0 → signℤ r ≡ ℤ.+_ 0
    ≈⇒0 = {!!}

    0⇒≈ : (r : ℝ) → signℤ r ≡ ℤ.+_ 0 → r ≈ fromℕ 0
    0⇒≈ = {!!}

    jonais : (r : ℝ)
           → let s = signℤ r ≡_ in
             s (ℤ.+_ 0) ⊎ s (ℤ.+_ 1) ⊎ s (ℤ.-_ $ ℤ.+_ 1)
    jonais = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}>\AgdaUnderscore}}}

\begin{code}
  module _>_ where
    ¬[r>r] : Irreflexive _≈_ _>_
    ¬[r>r] = {!!}

    r+s>r : (r s : ℝ) → s > fromℕ 0 → (r + s) > r
    r+s>r = {!!}

    >⇒¬< : Asymmetric _>_
    >⇒¬< = {!!}

    >⇒≉ : (r s : ℝ) → r > s → ¬_ $ r ≈ s
    >⇒≉ = {!!}

    ∃[>∧>⍨] : (r s : ℝ) → r > s → ∃ $ λ t → (r > t) × (t > s)
    ∃[>∧>⍨] r s z = frinu (r + s) (fromℕ 2) N , {!!} , {!!}
      where
      N = Fromℕ.fromℕ[s]≉0 1

    >∧>⇒> : Transitive _>_
    >∧>⇒> = {!!}

    >ℤ⇒> : (r s : ℝ) → ⌊' r ℤ.> ⌊' s → r > s
    >ℤ⇒> = {!!}

    +r>-s : {r s : ℝ}
          → sign r ≡ Sign.+
          → sign s ≡ Sign.-
            -- | ni'o sarcu ni'i zo'e joi le su'u li no na
            -- dubmau li no
          → ¬_ $ r ≈ fromℕ 0 × s ≈ fromℕ 0
          → r > s
    +r>-s = {!!}

    jonais : (r s : ℝ) → (r > s) ⊎ (s > r) ⊎ (r ≈ s)
    jonais = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}≥\AgdaUnderscore}}}

\begin{code}
  module _≥_ where
    ≥∧≥⇒≥ : Transitive _≥_
    ≥∧≥⇒≥ = {!!}

    ≥∧≥⍨⇒≈ : Relation.Binary.Antisymmetric _≈_ _≥_
    ≥∧≥⍨⇒≈ = {!!}

    ≈⇒≥ : {r s : ℝ} → r ≈ s → r ≥ s
    ≈⇒≥ = inj₁

    >⇒≥ : {r s : ℝ} → r > s → r ≥ s
    >⇒≥ = inj₂

    r≥r : Reflexive _≥_
    r≥r = ≈⇒≥ $ _≈_.≡⇒≈ refl

    ≥⇒¬< : {r s : ℝ} → r ≥ s → ¬_ $ r < s
    ≥⇒¬< = {!!}

    ≥∧≉⇒> : {r s : ℝ} → r ≥ s → ¬_ $ r ≈ s → r > s
    ≥∧≉⇒> (inj₁ d) N = d ⇒⇐ N
    ≥∧≉⇒> (inj₂ z) N = z

    ≥∧¬>⇒≈ : {r s : ℝ} → r ≥ s → ¬_ $ r > s → r ≈ s
    ≥∧¬>⇒≈ (inj₁ d) N = d
    ≥∧¬>⇒≈ (inj₂ z) N = z ⇒⇐ N

    +r>-s : {r s : ℝ}
          → ¬_ $ r ≈ fromℕ 0 × s ≈ fromℕ 0
          → sign r ≡ Sign.+
          → sign s ≡ Sign.-
          → r > s
    +r>-s = {!!}

    +r≥-s : {r s : ℝ}
          → sign r ≡ Sign.+
          → sign s ≡ Sign.-
          → r ≥ s
    +r≥-s = {!!}

    ⌊'r≥⌊'s⇒r≥s : {r s : ℝ}
                → ⌊' r ℤ.≥ ⌊' s
                → sign s ≡ Sign.+ ⊎ s ≈ fromℕ 0
                → r ≥ s
    ⌊'r≥⌊'s⇒r≥s = {!!}

    jonais : (r s : ℝ) → (r ≥ s) ⊎ (r < s)
    jonais r s with _>_.jonais r s
    ... | inj₁ z = inj₁ $ >⇒≥ z
    ... | inj₂ (inj₁ m) = inj₂ m
    ... | inj₂ (inj₂ d) = inj₁ $ inj₁ d

    ¬≥⇒< : {r s : ℝ} → ¬_ $ r ≥ s → r < s
    ¬≥⇒< {r} {s} N with jonais r s
    ... | inj₁ djm = djm ⇒⇐ N
    ... | inj₂ m = m
\end{code}

\subsection{\lcblm{\F{∣\AgdaUnderscore{}∣}}}

\begin{code}
  module ∣_∣ where
    r≥0⇒r≈∣r∣ : (r : ℝ) → r ≥ fromℕ 0 → r ≈ ∣ r ∣
    r≥0⇒r≈∣r∣ = {!!}

    0>r⇒∣r∣≈-r : (r : ℝ) → fromℕ 0 > r → ∣ r ∣ ≈_ $ ¯ r
    0>r⇒∣r∣≈-r = {!!}

    +r≡∣+r∣ : (r : ℝ) → sign r ≡ Sign.+ → r ≡ ∣ r ∣
    +r≡∣+r∣ r refl = refl

    ∣_∣≡∣_∣∘∣_∣ : Algebra.IdempotentFun _≡_ ∣_∣
    ∣_∣≡∣_∣∘∣_∣ _ = refl

    ∣_∣≈∣_∣∘∣_∣ : Algebra.IdempotentFun _≈_ ∣_∣
    ∣_∣≈∣_∣∘∣_∣ = _≈_.≡⇒≈ ∘ ∣_∣≡∣_∣∘∣_∣

    ≈⇒∣_∣≈ : Algebra.Congruent₁ _≈_ ∣_∣
    ≈⇒∣_∣≈ {r} {s} d with sign r , sign s
    ... | Sign.+ , Sign.+ = begin
      ∣ r ∣ ≈⟨ _≈_.≡⇒≈ $ sym $ +r≡∣+r∣ r {!!} ⟩
      r ≈⟨ d ⟩
      s ≈⟨ _≈_.≡⇒≈ $ +r≡∣+r∣ s {!!} ⟩
      ∣ s ∣ ∎
      where
      open import Relation.Binary.Reasoning.Setoid _≈_.setoid
    ... | Sign.+ , Sign.- = {!!}
    ... | Sign.- , Sign.+ = {!!}
    ... | Sign.- , Sign.- = {!!}

    jonais : (r : ℝ) → ∣ r ∣ ≈ r ⊎ ∣ r ∣ ≈ (¯ r)
    jonais = {!!}

    R[∣R∣] : (r : ℝ) → Rational r → Rational ∣ r ∣
    R[∣R∣] = {!!}

    I[∣I∣] : (r : ℝ) → Irrational r → Irrational ∣ r ∣
    I[∣I∣] = {!!}
\end{code}

\subsection{\lcblm{\F{\AgdaUnderscore{}⊓\AgdaUnderscore}}}

\begin{code}
  module _⊓_ where
    module I where
      open _⊓_I
        using (
          _≥ᵇ_;
          f
        )

      ≥⇒⊤ : {r s : ℝ} → r ≥ s → true ≡ _≥ᵇ_ r s
      ≥⇒⊤ = {!!}

      ⊤⇒≥ : (r s : ℝ) → true ≡ _≥ᵇ_ r s → r ≥ s
      ⊤⇒≥ = {!!}

      <⇒⊥ : (r s : ℝ) → s > r → false ≡ _≥ᵇ_ r s
      <⇒⊥ = {!!}

      ⊥⇒≤ : (r s : ℝ) → false ≡ _≥ᵇ_ r s → s ≥ r
      ⊥⇒≤ r s d with _≥_.jonais s r
      ... | inj₁ djm = djm
      ... | inj₂ z = d ⇒⇐ T⇒¬F (≥⇒⊤ {r} {s} $ _≥_.>⇒≥ z)
        where
        T⇒¬F : {x : Bool} → true ≡ x → ¬_ $ false ≡ x
        T⇒¬F refl ()

      ⊥⇒1 : ∀ {a} → {A : Set a} → (x z : A) → x ≡ f x z false
      ⊥⇒1 _ _ = refl

      ⊤⇒2 : ∀ {a} → {A : Set a}
          → (x : A)
          → {z : A}
          → z ≡ f x z true
      ⊤⇒2 _ = refl

    <⇒1 : (r s : ℝ) → r < s → r ≡ r ⊓ s
    <⇒1 r s m = subst (_≡_ r ∘ _⊓_I.f r s) (I.<⇒⊥ r s m) (I.⊥⇒1 r s)

    ≥⇒2 : (r s : ℝ) → r ≥ s → s ≡ r ⊓ s
    ≥⇒2 r s z = subst (_≡_ s ∘ _⊓_I.f r s) (I.≥⇒⊤ z) (I.⊤⇒2 r)

    ≈⇒1 : {r s : ℝ} → r ≈ s → r ≈ (r ⊓ s)
    ≈⇒1 = {!!}

    ≈⇒2 : {r s : ℝ} → r ≈ s → s ≈ (r ⊓ s)
    ≈⇒2 = {!!}

    ⊓≈⊓⍨ : Commutative _≈_ _⊓_
    ⊓≈⊓⍨ r s with _≥_.jonais r s
    ... | inj₁ djm = {!!}
    ... | inj₂ m = {!!}

    ⊓-ass : Associative _≈_ _⊓_
    ⊓-ass = {!!}

    ⊓-sel : Algebra.Selective _≡_ _⊓_
    ⊓-sel r s with _≥_.jonais r s
    ... | inj₁ djm = inj₂ $ sym $ ≥⇒2 r s djm
    ... | inj₂ ml = inj₁ $ sym $ <⇒1 r s ml

    id≈⊓⍨ : Algebra.Idempotent _≈_ _⊓_
    id≈⊓⍨ _ = _≈_.≈⇒≈⍨ $ ≈⇒1 $ _≈_.≡⇒≈ refl
\end{code}

\subsection{\lcblm{\F{fromℚ}}}

\begin{code}
  module Fromℚ where
    fromℚ-Rational : (k : ℚ) → Rational $ fromℚ k
    fromℚ-Rational k = k , _≈_.≡⇒≈ refl
\end{code}

\subsection{\lcblm{\F{Irrational}}}

\begin{code}
  module Irrational where
    R⊎I : (r : ℝ) → Rational r ⊎ Irrational r
    R⊎I = {!!}
\end{code}

\subsection{\lcblm{\F{toℚ}}}

\begin{code}
  module Toℚ where
    id≡toℚ∘fromℚ : (k : ℚ) → k ≡ toℚ {fromℚ k} (_ , _≈_.≡⇒≈ refl)
    id≡toℚ∘fromℚ _ = refl

    toℚ∘fromℕ : (n : ℕ)
              → let C = Coprime.sym $ Coprime.1-coprimeTo n in
                (_≡_
                  (toℚ {fromℕ n} $ Fromℕ.fromℕ-Rational n)
                  (ℚ.mkℚ (ℤ.+_ n) 0 C))
    toℚ∘fromℕ _ = refl

    toℚ∘fromℤ : (z : ℤ)
              → let C = Coprime.sym $ Coprime.1-coprimeTo ℤ.∣ z ∣ in
                (_≡_
                  (toℚ {fromℤ z} $ Fromℤ.fromℤ-Rational z)
                  (ℚ.mkℚ z 0 C))
    toℚ∘fromℤ = {!!}
\end{code}

\section{le ctaipe be le su'u sumji joi co'e me'oi .group.}

\begin{code}
+--group : Algebra.IsGroup _≈_ _+_ (fromℕ 0) (fromℕ 0 -_)
+--group = record {
  isMonoid = record {
    isSemigroup = {!!};
    identity = {!!}};
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
  *-isMonoid = record {
    isSemigroup = record {
      isMagma = Veritas._*_.*-magma;
      assoc = Veritas._*_.*-ass};
    identity = Veritas._*_.r≈1*r};
  distrib = {!!};
  zero = Veritas._*_.0≈0*r}
\end{code}
\end{document}
