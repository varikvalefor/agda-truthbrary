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
\newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_v}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal{\uplus}}}
\newunicodechar{≡}{\ensuremath{\mathnormal{\equiv}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\land}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\stackrel{?}{=}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Record.SR}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o sa'u ko'a goi la'o zoi.\ \texttt\cmene .zoi.\ vasru zo'e poi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ kei je lo nu lo ctaipe be la'oi .\F{String}.\ cu binxo pe'a ru'e

.i sa'u nai ru'e vasru\ldots
\begin{itemize}
	\item vu'oi la'oi .\F{Show}.\ je la'oi .\F{show}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Show}.\ vu'o noi tu'a ke'a filri'a lo nu binxo pe'a ru'e lo ctaipe be la'oi .\F{String}.\ ku'o je
        \item vu'oi la'oi .\F{Read}.\ je la'oi .\F{readmaybe}.\ je le me'oi .\AgdaKeyword{instance}.\ pe la'oi .\F{Read}.\ vu'o noi tu'a ke'a filri'a lo nu lo me'oi .\F{Maybe}.\ ctaipe cu selbi'o pe'a ru'e lo ctaipe be la'oi .\F{String}.
\end{itemize}

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Record.SR where

open import Data.Fin
  hiding (
    _≟_;
    toℕ
  )
open import Data.Nat
  hiding (
    _≟_
  )
open import Data.Sum
  using (
    _⊎_;
    inj₁;
    inj₂
  )
open import Function
open import Data.Bool
  hiding (
    _≟_
  )
open import Data.Char
  using (
    Char;
    toℕ;
    fromℕ
  )
open import Data.List
  using (
    List;
    null;
    _∷_
  )
open import Data.Float
  using (
    Float
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.String
  hiding (
    _≟_;
    show;
    length;
    _++_
  )
open import Data.Integer
  using (
    +_;
    ℤ
  )
open import Data.Fin.Show
  using (
  )
open import Data.Nat.Show
  using (
  )
open import Truthbrary.Record.Eq
open import Truthbrary.Record.LLC
  hiding (
    _∷_
  )
open import Relation.Nullary.Decidable
  using (
    isNo;
    isYes
  )
open import Relation.Binary.PropositionalEquality
\end{code}

\section{la'oi .\F{Show}.}
ni'o ga naja la'o zoi.\ \B S .zoi.\ fa'u la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \F{Show} \B A .zoi.\ fa'u la'o zoi.\ \B A .zoi.\ gi la'o zoi.\ \F{Show.show} \B S \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.

\begin{code}
record Show {a} (A : Set a) : Set a
  where
  field
    show : A → String
\end{code}

\subsection{la'oi .\F{show}.}
ni'o ga naja la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B A .zoi.\ gi la'o zoi.\ \F{show} \B a .zoi.\ sinxa la'o zoi.\ \B a .zoi.

\begin{code}
show : ∀ {a} → {A : Set a} → ⦃ Show A ⦄
     → A → String
show ⦃ boob ⦄ = Show.show boob
\end{code}

\subsection{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  showℕ = record {show = Data.Nat.Show.show}
  showFin : {n : ℕ} → Show $ Fin n
  showFin = record {show = Data.Fin.Show.show}
  showChar = record {show = Data.Char.show}
  showString = record {show = Data.String.show}
  showMaybe : ∀ {a} → {A : Set a}
            → ⦃ Show A ⦄
            → Show $ Maybe A
  showMaybe {_} {A} = record {show = funk}
    where
    funk : Maybe A → String
    funk nothing = "nothing"
    funk (just t) = "just " ++ parens (show t)
  showSum : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Show A ⦄ → ⦃ Show B ⦄
          → Show $ A ⊎ B
  showSum {_} {_} {A} {B} = record {show = stank}
    where
    stank : A ⊎ B → String
    stank (inj₁ pa) = "inj₁ " ++ parens (show pa)
    stank (inj₂ re) = "inj₂ " ++ parens (show re)
\end{code}

\section{la'oi .\F{Read}.}
\newcommand\rmvvc{ga jonai ga je lo te samrkompli ja zo'e cu djuno lo du'u la'o zoi. \B b .zoi.\ sinxa ma kau gi ko'a goi la'o zoi.\ \F{Read.readMaybe} \F Q \B b .zoi.\ me'oi .\F{just}.\ lo selsni be la'o zoi.\ \B b .zoi.\ gi ko'a du la'oi .\F{nothing}.}
ni'o ga jo ga je la'o zoi.\ \B Q .zoi.\ ctaipe la'o zoi.\ \F{Read} \B A .zoi.\ gi la'o zoi.\ \B a .zoi.\ ctaipe la'o zoi.\ \B a .zoi.\ gi \rmvvc

\begin{code}
record Read {a} (A : Set a) : Set a
  where
  field
    readMaybe : String → Maybe A
\end{code}

\subsection{la'oi .\F{readMaybe}.}
ni'o \rmvvc

\begin{code}
readMaybe : ∀ {a} → {A : Set a} → ⦃ Read A ⦄
          → String → Maybe A
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
    stedu=<< = flip _>>=_ Data.String.head
  -- | .i pilno li pano ki'u le nu pruce le te pruce
  -- be le me'oi .show. co'e pe la'oi .ℕ.
  readℕ = record {readMaybe = Data.Nat.Show.readMaybe 10}
  readℤ : Read ℤ
  readℤ = record {readMaybe = f ∘ toList}
    where
    f : List Char → Maybe ℤ
    f List.[] = nothing
    f (x ∷ xs) = if isYes (x ≟ '-') then mapₘ n r else mapₘ p r'
      where
      r r' : Maybe ℕ
      r = readMaybe $ fromList xs
      r' = readMaybe $ fromList $ x ∷ xs
      p = Data.Integer.+_
      n = Data.Integer.-_ ∘ p
  readFloat : Read Float
  readFloat = record {readMaybe = exp ∘ spit ∘ Data.String.toList}
    where
    spit : List Char → List $ List $ List Char
    spit = map (splitOn '.') ∘ splitOn 'e'
      where
      splitOn : ∀ {a} → {A : Set a}
              → ⦃ Eq A ⦄
              → A → List A → List $ List A
      splitOn a = rev ∘ map rev ∘ sob a [] []
        where
        rev = Data.List.reverse
        sob : ∀ {a} → {A : Set a}
            → ⦃ Eq A ⦄
            → A → List $ List A → List A → List A
            → List $ List A
        sob a b g (f ∷ xs) = if isYes (f ≟ a) then hitit else add
          where
          hitit = sob a (g ∷ b) [] xs
          add = sob a b (f ∷ g) xs
        sob a b g Data.List.[] = g ∷ b
    n2f = Data.Float.fromℤ
    p : List $ List Char → Maybe Float
    p (a ∷ List.[]) = mapₘ Data.Float.fromℕ $ readMaybe $ fromList a
    p (a ∷ b ∷ List.[]) = comb (rM a) (rM b)
      where
      -- | .i filri'a lo nu genturfa'i pe'a ru'e fi zoi zoi.
      -- .1 .zoi. je zoi zoi. 1. .zoi. je zoi zoi. . .zoi.
      rM = λ q → if null q then just (+_ 0) else readMaybe (fromList q)
      comb : Maybe ℤ → Maybe ℤ → Maybe Float
      comb (just x) (just y) = just $ _+f_ (n2f x) $ n2f y ÷ sf b
        where
        pos = isNo $ Data.List.head a ≟ just '-'
        _+f_ = if pos then Data.Float._+_ else Data.Float._-_
        _÷_ = Data.Float._÷_
        sf = Data.Float._**_ (n2f $ +_ 10) ∘ n2f ∘ +_ ∘ length
      comb _ _ = nothing
    p _ = nothing
    exp : List $ List $ List Char → Maybe Float
    exp (t ∷ List.[]) = p t
    exp (t ∷ (x ∷ List.[])) = liftM2 dt10 (p t) $ p x
      where
      liftM2 : ∀ {a b} → {A : Set a} → {B : Set b}
             → (A → A → B) → Maybe A → Maybe A → Maybe B
      liftM2 f (just a) (just b) = just $ f a b
      liftM2 _ _ _ = nothing
      dt10 = λ a b → a Data.Float.* n2f (+_ 10) Data.Float.** b
    exp _ = nothing
  -- | .i pilno li pano ki'u le nu pruce le te pruce
  -- be le me'oi .show. co'e pe la'oi .Fin.
  readFin : {n : ℕ} → Read $ Fin n
  readFin = record {readMaybe = Data.Fin.Show.readMaybe 10}
  readMayb : ∀ {a} → {A : Set a} → ⦃ Read A ⦄
           → Read $ Maybe A
  readMayb {_} {A} ⦃ X ⦄  = record {readMaybe = Q ∘ toList}
    where
    Q : List Char → Maybe $ Maybe A
    Q t = if justice then just (t' >>= readMaybe) else nada
      where
      -- | ni'o su'o da zo'u nandu fa lo nu jimpe fi da
      tim = fromList t == "nothing"
      justice = fromList (Data.List.take 5 t) == "just "
      nada = if tim then just nothing else nothing
      t' = unparens $ fromList $ Data.List.drop 5 t
  readSum : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Read A ⦄ → ⦃ Read B ⦄
          → Read $ A ⊎ B
  readSum {_} {_} {A} {B} = record {readMaybe = inj₁?}
    where
    inj₁? : String → Maybe $ A ⊎ B
    inj₁? q = if t5 == "inj₁ " then inj inj₁ else inj2?
      where
      apf : (List Char → List Char) → String
      apf f = fromList $ f $ toList q
      t5 = apf $ Data.List.take 5
      d5 = apf $ Data.List.drop 5
      inj : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ Read A ⦄
          → (A → B) → Maybe B
      inj f = unparens d5 >>= mapₘ f ∘ readMaybe
      inj2? = if t5 == "inj₂ " then inj inj₂ else nothing
\end{code}

\section{la'oi .\F{SR}.}
ni'o ga jo zasti fa lo ctaipe be la'o zoi.\ \F{SR} \B Q .zoi.\ gi ga naja la'o zoi.\ \B q .zoi.\ ctaipe la'o zoi.\ \B Q .zoi.\ gi la'o zoi.\ \F{readMaybe} \Sym\$ \F{show} \B q .zoi.\ du la'o zoi.\ \F{just} \B q .zoi.

\subsection{le cmene be le me'oi .\AgdaKeyword{field}.}
ni'o la .varik.\ cu xamsku zo'oi .\F{fat}.\ noi ke'a me'oi .\AgdaKeyword{field}.\ je ku'i cu na mutce le ka ce'u .anci\ldots kei je ku'i cu sorpa'a lo nu lo tcidu cu jimpe fi le se xamsku

\begin{code}
record SR {a} (A : Set a) ⦃ Q : Read A ⦄ ⦃ R : Show A ⦄ : Set a
  where
  field
    fat : just ≡ Read.readMaybe Q ∘ Show.show R
\end{code}
\end{document}
