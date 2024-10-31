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
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal{\divdot}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Record.SR}

\title{la'o zoi.\ \AgdaModule{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o sa'u ko'a goi la'o zoi.\ \AgdaModule\cmene .zoi.\ vasru lo jai filri'a be lo nu binxo pe'a ru'e lo ctaipe be la'oi .\AgdaPostulate{String}.\ kei je lo nu lo ctaipe be la'oi .\AgdaPostulate{String}.\ cu binxo pe'a ru'e

.i sa'u nai ru'e vasru\ldots
\begin{itemize}
	\item vu'oi la'oi .\AgdaRecord{Show}.\ je la'oi .\F{show}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\AgdaRecord{Show}.\ vu'o noi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\AgdaPostulate{String}.\ ku'o je
        \item vu'oi la'oi .\AgdaRecord{Read}.\ je la'oi .\F{readMaybe}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\AgdaRecord{Read}.\ vu'o noi ke'a jai filri'a lo nu lo me'oi .\D{Maybe}.\ ctaipe cu selbi'o pe'a ru'e lo ctaipe be la'oi .\AgdaPostulate{String}.
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}
{-# OPTIONS --instance-search-depth=2 #-}
{-# OPTIONS --backtracking-instance-search #-}

module Truthbrary.Record.SR where

import Data.Integer.Show
import Data.Rational.Show

open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    _∸_;
    ℕ
  )
open import Data.Sum
  using (
    inj₁;
    inj₂;
    _⊎_
  )
open import Function
  using (
    _on_;
    flip;
    _$_;
    _∘_
  )
open import Data.Bool
  using (
    if_then_else_;
    false;
    true;
    Bool;
    not
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    null;
    _∷_
  )
open import Data.Float
  as Flot
  using (
    Float
  )
open import Data.Maybe
  as ？
  using (
    nothing;
    _>>=_;
    Maybe;
    maybe;
    just
  )
  renaming (
    map to mapₘ
  )
open import Data.String
  using (
    fromList;
    toList;
    parens;
    String
  )
open import Data.Integer
  using (
    +_;
    ℤ
  )
open import Data.Rational
  as ℚ
  using (
    mkℚ;
    ℚ
  )
open import Data.Fin.Show
  using (
  )
open import Data.Nat.Show
  using (
  )
open import Data.Maybe.Instances
  using (
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_
  )
open import Truthbrary.Record.LLC
  using (
    length;
    decaf;
    _++_
  )
open import Truthbrary.Category.Monad
  using (
    _>=>_
  )
  renaming (
    map₂ to liftM2
  )
open import Data.Rational.Unnormalised
  as ℚᵘ
  using (
    mkℚᵘ;
    ℚᵘ
  )
open import Relation.Nullary.Decidable
  using (
    isNo
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )
\end{code}

\section{la'oi .\AgdaRecord{Show}.}
ni'o ga naja la'o zoi.\ \B S .zoi.\ fa'u la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Show} \B A .zoi.\ fa'u la'o zoi.\ \B A .zoi.\ gi la'o zoi.\ \AgdaField{Show.show} \B S \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.

\begin{code}
record Show {a} (A : Set a) : Set a
  where
  field
    show : A → String
\end{code}

\subsection{la'oi .\F{show}.}
ni'o ga janai la'o zoi.\ \F{show} \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.\ gi ga je ctaipe la'o zoi.\ \AgdaRecord{Show} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B A .zoi.

\begin{code}
show : ∀ {a} → {A : Set a} → ⦃ Show A ⦄ → A → String
show ⦃ boob ⦄ = Show.show boob
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  showℕ = record {show = Data.Nat.Show.show}
  showFloat = record {show = Flot.show}
  showFin : {n : ℕ} → Show $ Fin n
  showFin = record {show = Data.Fin.Show.show}
  showChar = record {show = Data.Char.show}
  showString = record {show = Data.String.show}
  showℤ = record {show = Data.Integer.Show.show}
  showℚ : Show ℚ
  showℚ = record {show = Data.Rational.Show.show}
  showℚᵘ : Show ℚᵘ
  showℚᵘ = record {show = f}
    where
    f : ℚᵘ → String
    f k = show (ℚᵘ.numerator k) ++ "/" ++ show (ℚᵘ.denominator k)
  showMaybe : ∀ {a} → {A : Set a} → ⦃ Show A ⦄ → Show $ Maybe A
  showMaybe = record {show = funk}
    where
    funk = maybe (("just " ++_) ∘ parens ∘ show) "nothing"
  showSum : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Show A ⦄ → ⦃ Show B ⦄
          → Show $ A ⊎ B
  showSum = record {show = stank}
    where
    stank : _ → String
    stank (inj₁ pa) = "inj₁ " ++ parens (show pa)
    stank (inj₂ re) = "inj₂ " ++ parens (show re)
\end{code}

\section{la'oi .\AgdaRecord{Read}.}
\newcommand\rmvvc{ga jonai la'oi .\AgdaInductiveConstructor{nothing}.\ du ko'a goi la'o zoi.\ \AgdaField{Read.readMaybe} \B Q \B b .zoi.\ gi ga je lo te samrkompli ja zo'e cu djuno lo du'u la'o zoi.\ \B b .zoi.\ sinxa ma kau gi ko'a me'oi .\AgdaInductiveConstructor{just}.\ lo selsni be la'o zoi.\ \B b .zoi.}
ni'o ga jo ga je la'o zoi.\ \B Q .zoi.\ ctaipe la'o zoi.\ \AgdaRecord{Read} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B a .zoi.\ gi \rmvvc

\begin{code}
record Read {a} (A : Set a) : Set a
  where
  field
    readMaybe : String → Maybe A
\end{code}

\subsection{la'oi .\F{readMaybe}.}
ni'o \rmvvc

\begin{code}
readMaybe : ∀ {a} → {A : Set a}
          → ⦃ Read A ⦄
          → String
          → Maybe A
readMaybe ⦃ drivel ⦄ = Read.readMaybe drivel
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
private
  unparens : String → Maybe String
  unparens = decaf '(' ')'

instance
  readChar : Read Char
  readChar = record {readMaybe = stedu=<< ∘ decaf '\'' '\''}
    where
    stedu=<< = _>>= Data.String.head
  -- | .i pilno li pano ki'u le su'u pruce lo te pruce
  -- be le me'oi .show. co'e pe la'oi .ℕ.
  readℕ : Read ℕ
  readℕ = record {readMaybe = Data.Nat.Show.readMaybe 10}
  readℤ : Read ℤ
  readℤ = record {readMaybe = f ∘ toList}
    where
    f : List Char → Maybe ℤ
    f 𝕃.[] = nothing
    f ('-' ∷ xs) = mapₘ n $ readMaybe $ fromList xs
      where
      n = Data.Integer.-_ ∘ +_
    f x@(_ ∷ _) = mapₘ +_ $ readMaybe $ fromList x
  readℚᵘ : Read ℚᵘ
  readℚᵘ = record {readMaybe = f ∘ splitOn '/' ∘ toList}
    where
    f : List $ List Char → Maybe ℚᵘ
    f (x ∷ 𝕃.[]) = mapₘ (flip mkℚᵘ 1) $ readMaybe $ fromList x
    f (x ∷ z ∷ List.[]) = liftM2 mkℚᵘ (readMaybe $ fromList x) z'
      where
      rm = readMaybe $ fromList z
      rmy = if rm ≡ᵇ just 0 then nothing else rm
      z' = maybe (just ∘ flip _∸_ 1) nothing rmy
    f _ = nothing
  readℚ : Read ℚ
  readℚ = record {readMaybe = readMaybe >=> f}
    where
    norm = show ∘ ℚ.toℚᵘ ∘ ℚ.fromℚᵘ
    f = λ x → if norm x ≡ᵇ show x then just (ℚ.fromℚᵘ x) else nothing
  readFloat : Read Float
  readFloat = record {readMaybe = exp ∘ spit ∘ Data.String.toList}
    where
    spit = 𝕃.map (splitOn '.') ∘ splitOn 'e'
    n2f = Flot.fromℤ
    p : List $ List Char → Maybe Float
    p (a ∷ List.[]) = mapₘ Flot.fromℕ $ readMaybe $ fromList a
    p (a ∷ b ∷ List.[]) = (comb on rM) a b
      where
      -- | .i filri'a lo nu genturfa'i pe'a ru'e zoi zoi.
      -- .1 .zoi. je zoi zoi. 1. .zoi. je zoi zoi. . .zoi.
      rM = λ q → if null q then just (+ 0) else readMaybe (fromList q)
      comb = liftM2 $ λ x y → (n2f x) +f_ $ n2f y ÷ sf b
        where
        pos = not $ 𝕃.head a ≡ᵇ just '-'
        _+f_ = if pos then Flot._+_ else Flot._-_
        _÷_ = Flot._÷_
        sf = Flot._**_ (n2f $ + 10) ∘ n2f ∘ +_ ∘ length
    p _ = nothing
    exp : List $ List $ List Char → Maybe Float
    exp (t ∷ List.[]) = p t
    exp (t ∷ x ∷ List.[]) = (liftM2 dt10 on p) t x
      where
      dt10 = λ a b → a Flot.* n2f (+_ 10) Flot.** b
    exp _ = nothing
  -- | .i pilno li pano ki'u le nu pruce lo te pruce
  -- be le me'oi .show. co'e pe la'oi .Fin.
  readFin : {n : ℕ} → Read $ Fin n
  readFin = record {readMaybe = Data.Fin.Show.readMaybe 10}
  readMayb : ∀ {a} → {A : Set a} → ⦃ Read A ⦄ → Read $ Maybe A
  readMayb {A = A} = record {readMaybe = Q ∘ toList }
    where
    Q : List Char → Maybe $ Maybe A
    Q ('n' ∷ 'o' ∷ 't' ∷ 'h' ∷ 'i' ∷ 'n' ∷ 'g' ∷ 𝕃.[]) = just nothing
    Q ('j' ∷ 'u' ∷ 's' ∷ 't' ∷ ' ' ∷ x) = ？.map readMaybe $ unparens x'
      where
      x' = fromList x
    -- | ni'o su'o da zo'u nandu fa lo nu jimpe fi da
    Q _ = nothing
  readSum : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Read A ⦄ → ⦃ Read B ⦄
          → Read $ A ⊎ B
  readSum {A = A} {B} = record {readMaybe = inj₁?}
    where
    inj₁? : String → Maybe $ A ⊎ B
    inj₁? s = if t5 ≡ᵇ "inj₁ " then rmap inj₁ else inj2?
      where
      apf : (List Char → List Char) → String
      apf f = fromList $ f $ toList s
      L = length "inj₁ " -- .i du la'o zoi. length "inj₂ " .zoi.
      t5 = apf $ 𝕃.take L
      d5 = apf $ 𝕃.drop L
      rmap : ∀ {a b} → {A : Set a} → {B : Set b}
           → ⦃ Read A ⦄
           → (A → B)
           → Maybe B
      rmap f = unparens d5 >>= mapₘ f ∘ readMaybe
      inj2? = if t5 ≡ᵇ "inj₂ " then rmap inj₂ else nothing
\end{code}

\section{la'oi .\AgdaRecord{SR}.}
ni'o ga jo zasti fa lo ctaipe be la'o zoi.\ \AgdaRecord{SR} \B Q .zoi.\ gi ga naja la'o zoi.\ \B q .zoi.\ ctaipe la'o zoi.\ \B Q .zoi.\ gi la'o zoi.\ \F{readMaybe} \Sym\$ \F{show} \B q .zoi.\ du la'o zoi.\ \AgdaInductiveConstructor{just} \B q .zoi.

\subsection{le cmene be le me'oi .\AgdaKeyword{field}.}
ni'o la .varik.\ cu xamsku zoi zoi.\ \AgdaField{SR.fat} .zoi.\ noi ke'a cmene le me'oi .\AgdaKeyword{field}.\ je ku'i cu na mutce le ka ce'u .anci\ldots kei je ku'i cu sorpa'a lo nu lo tcidu cu jimpe fi le se xamsku

\begin{code}
record SR {a} (A : Set a) ⦃ Q : Read A ⦄ ⦃ R : Show A ⦄ : Set a
  where
  field
    fat : just ≡ Read.readMaybe Q ∘ Show.show R
\end{code}
\end{document}
