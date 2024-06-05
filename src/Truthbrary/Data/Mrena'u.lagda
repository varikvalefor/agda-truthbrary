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
\newunicodechar{ℝ}{\ensuremath{\mathnormal{\mathbb{R}}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb{Z}}}}
\newunicodechar{ℂ}{\ensuremath{\mathnormal{\mathbb{C}}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb{B}}}}
\newunicodechar{ν}{\ensuremath{\mathnormal{\nu}}}
\newunicodechar{μ}{\ensuremath{\mathnormal{\mu}}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
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
\newunicodechar{≈}{\ensuremath{\mathnormal{\approx}}}
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

module Truthbrary.Data.Mrena'u where

open import Algebra
  using (
    Associative;
    Commutative
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
open import Function
  using (
    const;
    _∘_;
    _$_
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
    _,_
  )
open import Relation.Binary
  using (
    Asymmetric 
  )
open import Relation.Nullary
  using (
    ¬_
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≗_;
    _≡_
  )

import Level
\end{code}

\section{la'oi .\F ℝ.}
ni'o la'oi .\F ℝ.\ ctaipe lo ro mrena'u\ldots\ jenai zo'e  .i la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \B s \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore{}}\B a \B b\Sym)\ .zoi.\ poi ke'a ctaipe la'oi .\F ℝ.\ cu lo pilji be lo sumji be la'oi .\B a.\ bei lo mu'oi glibau.\ decimal expansion .glibau.\ namcu be la'oi .\B b.\ be'o be'o be'o bei zo'e poi ga jonai ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.+}\ .zoi.\ gi ke'a du li pa gi ga je la'oi .\B s.\ du la'o zoi.\ \IC{Sign.-}\ .zoi.\ gi ke'a du li ni'u pa  .i ga jo ko'a goi la'o zoi.\ \IC{\AgdaUnderscore{},\AgdaUnderscore} \AgdaUnderscore{} \Sym(\IC{\AgdaUnderscore{},\AgdaUnderscore} \B a \B f\Sym)\ .zoi.\ gi la'o zoi.\ \B f \B n\ .zoi.\ meirmoi la'oi .\B n.\ fo lo me'oi .digit.\ be lo cmalu pagbu be lo mu'oi glibau.\ decimal expansion .glibau.\ be ko'a

.i la .varik.\ cu pacna lo nu frili cumki fa lo nu xagzengau pe'a le velcki

\begin{code}
ℝ : Set
ℝ = Sign × ℕ × (ℕ → Digit 10)
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≈\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B r \OpF ≈ \B s\ .zoi.\ gi la'oi .\B r.\ namcu du la'oi .\B s.

\begin{code}
_≈_ : ℝ → ℝ → Set
_≈_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _≈_Veritas where
  ≡⇒≈ : (r s : ℝ) → r ≡ s → r ≈ s
  ≡⇒≈ = {!!}

  n+1≈n,9+ : (n : ℕ)
           → let 3F = 𝔽.suc $ 𝔽.suc $ 𝔽.suc 𝔽.zero in
             let 6F = 𝔽.suc $ 𝔽.suc $ 𝔽.suc 3F in
             let 9F = 𝔽.suc $ 𝔽.suc $ 𝔽.suc 6F in
             (_≈_
               (Sign.+ , (ℕ.suc n) , const 𝔽.zero)
               (Sign.+ , n , const 9F))
  n+1≈n,9+ = {!!}

  >⇒¬≈ : (r s : ℝ)
       → let ℤp = (Function._∋_
                    (ℝ → ℤ)
                    (λ {(Sign.+ , n , x) → ℤ.+_ n;
                        (Sign.- , n , x) → ℤ.-_ (ℤ.+_ n)})) in
         ℤ.∣ ℤp r ℤ.- ℤp s ∣ ℕ.> 1
       → ¬_ $ r ≈ s
  >⇒¬≈ = {!!}

  ¬[fn≡gn]⇒¬≈ : (r s : ℝ)
              → proj₁ r ≡ proj₁ s
              → let fp = proj₂ ∘ proj₂ in
                ¬_ $ fp r ≗ fp s
              → ¬_ $ r ≈ s
  ¬[fn≡gn]⇒¬≈ = {!!}
\end{code}

\section{la'o zoi.\ \F{fromℕ} .zoi.}
ni'o la'o zoi.\ \F{fromℕ} \B n\ .zoi.\ namcu du la'oi .\B n.

\begin{code}
fromℕ : ℕ → ℝ
fromℕ n = Sign.+ , n , const 𝔽.zero
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module FromℕVeritas where
  pav : (n : ℕ) → n ≡ proj₁ (proj₂ $ fromℕ n)
  pav _ = _≡_.refl

  rel : (m n : ℕ) → 𝔽.zero ≡ proj₂ (proj₂ $ fromℕ m) n
  rel = {!!}
\end{code}

\section{la'o zoi.\ \F{fromℤ}\ .zoi.}
ni'o la'o zoi.\ \F{fromℤ} \B z\ .zoi.\ namcu dunli la'oi .\B z.

\begin{code}
fromℤ : ℤ → ℝ
fromℤ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}+\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF + \B b\ .zoi.\ sumji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_+_ : ℝ → ℝ → ℝ
_+_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _+_Veritas where
  +≡+⍨ : Associative {ℓ = Level.zero} {!!} _+_
  +≡+⍨ = {!!}

  +-comm : Commutative {ℓ = Level.zero} {!!} _+_
  +-comm = {!!}

  id≡+0 : (r : ℝ) → r ≡ r + fromℕ 0
  id≡+0 = {!!}

  dratadratas : (r s : ℝ)
              → ¬_ $ r ≡ s
              → let N = ¬_ ∘ _≡_ (r + s) in
                N r × N s
  dratadratas = {!!}

  r≡r₁+r₂ : (r : ℝ)
          → (_≡_
              r
              (_+_
                (proj₁ r , proj₁ (proj₂ r) , const 𝔽.zero)
                (Sign.+ , 0 , proj₂ (proj₂ r))))
  r≡r₁+r₂ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}-\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF - \B b\ .zoi.\ vujnu la'oi .\B a.\ la'oi .\B b.

\begin{code}
_-_ : ℝ → ℝ → ℝ
_-_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _-_Veritas where
  r≈-r⇒r≡0 : (r : ℝ)
           → r ≈ (fromℕ 0 - r)
           → r ≡ fromℕ 0
  r≈-r⇒r≡0 = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}*\AgdaUnderscore}\ .zoi.}
ni'o la'o zoi.\ \B a \OpF * \B b\ .zoi.\ pilji la'oi .\B a.\ la'oi .\B b.

\begin{code}
_*_ : ℝ → ℝ → ℝ
_*_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _*_Veritas where
  r≈1*r : (r : ℝ) → r ≈_ $ fromℕ 1 * r
  r≈1*r = {!!}

  0≈0*r : (r : ℝ) → fromℕ 0 ≈ (fromℕ 0 * r)
  0≈0*r = {!!}
\end{code}

\section{la \F{frinu}}
ni'o la'o zoi.\ \F{frinu} \B a \B b\ .zoi.\ frinu la'oi .\B a.\ la'oi .\B b.

\begin{code}
frinu : (_ d : ℝ) → ¬_ $ d ≡ fromℕ 0 → ℝ
frinu = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module FrinuVeritas where
  sez≡1 : (r : ℝ) → (N : _) → frinu r r N ≡ fromℕ 1
  sez≡1 = {!!}

  r≡r/1 : (r : ℝ) → r ≡ frinu r (fromℕ 1) (λ ())
  r≡r/1 = {!!}

  0≡0/r : (r : ℝ) → (N : _) → fromℕ 0 ≡ frinu (fromℕ 0) r N
  0≡0/r = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}\textasciicircum{}\AgdaUnderscore}\ .zoi.}
ni'o tenfa la'oi .\B a.\ la'oi .\B b.\ fa la'o zoi.\ \B a \OpF \textasciicircum{} \B b\ .zoi.

\begin{code}
_^_ : ℝ → ℝ → ℝ
_^_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _^_Veritas where
  id≡_^1 : (r : ℝ) → r ≡ r ^ fromℕ 1
  id≡_^1 = {!!}

  0≡0^r : (r : ℝ) → fromℕ 0 ≡ fromℕ 0 ^ r
  0≡0^r = {!!}

  [r^s]^t≈r^[s*t] : (r s t : ℝ) → ((r ^ s) ^ t) ≈ (r ^ (s * t))
  [r^s]^t≈r^[s*t] = {!!}

  r≡[r^s]^[1/s] : (r s : ℝ)
                → (N : _)
                → (_≡_
                    r
                    (_^_
                      (r ^ s)
                      (frinu (fromℕ 1) s N)))
  r≡[r^s]^[1/s] = {!!}
\end{code}

\section{la'o zoi.\ \F{∣\AgdaUnderscore{}∣}\ .zoi.}
ni'o cu'alni la'oi .\B r.\ fa la'o zoi.\ \F{∣\AgdaUnderscore{}∣} \B r\ .zoi.

\begin{code}
∣_∣ : ℝ → ℝ
∣_∣ = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}>\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF{>} \B b\ .zoi.\ gi la'oi .\B a.\ zmadu la'oi .\B b.

\begin{code}
_>_ : ℝ → ℝ → Set
_>_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _>_Veritas where
  ¬sez : (r : ℝ) → ¬_ $ r > r
  ¬sez = {!!}

  zmad : (r s : ℝ) → s > fromℕ 0 → (r + s) > r
  zmad = {!!}

  >⇒¬< : Asymmetric _>_
  >⇒¬< = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}≥\AgdaUnderscore}\ .zoi.}
ni'o ga jo ctaipe la'o zoi.\ \B a \OpF ≥ \B b\ .zoi.\ gi la'oi .\B a.\ dubjavmau la'oi .\B b.

\begin{code}
_≥_ : ℝ → ℝ → Set
_≥_ = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
module _≥_Veritas where
  sez : (r : ℝ) → r ≥ r
  sez = {!!}

  >⇒≥ : (r s : ℝ) → r > s → r ≥ s
  >⇒≥ = {!!}

  ∃[≥∧≥⍨] : (r s : ℝ)
          → (Data.Product.∃
              (λ t → _×_
                (s ≥ t)
                (t ≥ r)))
  ∃[≥∧≥⍨] = {!!}
\end{code}
\end{document}
