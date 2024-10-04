\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{selnolig}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\nolig{>>}{>|>}
\nolig{<<}{<|<}

\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\mathnormal{\forall}}}
\newunicodechar{λ}{\ensuremath{\mathnormal{\lambda}}}
\newunicodechar{→}{\ensuremath{\mathnormal{\rightarrow}}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\!\lbrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rbrace\!\rbrace}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\newcommand\cmene{Truthbrary.Category.Monad}
\newcommand\liharmi{ni'o la .varik. cu jinvi le du'u le se ctaipe cu xamgu velcki}

\title{la'o zoi.\ \texttt{\cmene} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\section{le me'oi .abstract.}
ni'o la'o zoi.\ \texttt{\cmene} .zoi.\ vasru le velcki be le fancu poi tu'a ke'a filri'a tu'a lo me'oi .\F{RawMonad}.

\section{le vrici}

\begin{code}
{-# OPTIONS --safe #-}

module Truthbrary.Category.Monad where

open import Level
open import Data.Nat
open import Data.Sum
  using (
    [_,_];
    _⊎_;
    inj₁;
    inj₂
  )
open import Function
open import Category.Monad
\end{code}

\section{la'oi .\F{pure}.}
\liharmi

\begin{code}
pure : ∀ {a} → {A : Set a}
     → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
     → A → M A
pure ⦃ idiocy ⦄ = RawMonad.pure idiocy
\end{code}

\section{la'oi .\F{\AgdaUnderscore>>=\AgdaUnderscore}.}
\liharmi

\begin{code}
_>>=_ : ∀ {a} → {A B : Set a}
      → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
      → M A
      → (A → M B)
      → M B
_>>=_ ⦃ ssmw ⦄ = RawMonad._>>=_ ssmw
\end{code}

\section{la'oi .\F{\AgdaUnderscore=<<\AgdaUnderscore}.}
\liharmi

\begin{code}
_=<<_ : ∀ {a} → {A B : Set a}
      → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
      → (A → M B) → M A → M B
_=<<_ = flip _>>=_
\end{code}

\section{la'oi .\F{\AgdaUnderscore>=>\AgdaUnderscore}.}
\liharmi

\begin{code}
_>=>_ : ∀ {a} → {A B C : Set a}
      → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
      → (A → M B) → (B → M C) → A → M C
_>=>_ f g = _=<<_ g ∘ f
\end{code}

\section{la'oi .\F{\AgdaUnderscore{}<=<\AgdaUnderscore}.}
\liharmi

\begin{code}
_<=<_ : ∀ {a} → {A B C : Set a}
      → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
      → (B → M C)
      → (A → M B)
      → A
      → M C
_<=<_ = flip _>=>_
\end{code}

\section{la'oi .\F{map}.}
\liharmi

\begin{code}
map : ∀ {a} → {A B : Set a}
    → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
    → (A → B) → M A → M B
map f = _=<<_ $ pure ∘ f
\end{code}

\section{la'oi .\F{map₂}.}
\liharmi

\begin{code}
map₂ : ∀ {a} → {A B C : Set a}
     → {M : Set _ → Set _} → ⦃ RawMonad M ⦄
     → (A → B → C)
     → M A
     → M B
     → M C
map₂ f a b = a >>= λ a' → map (f a') b
\end{code}

\section{le me'oi .\AgdaKeyword{instance}.}

\begin{code}
instance
  ⊎Monad : ∀ {a} → {A : Set a} → RawMonad $ _⊎_ A
  ⊎Monad = record {return = inj₂; _>>=_ = _>>=⊎_}
    where
    _>>=⊎_ : ∀ {a} → {A B C : Set a}
           → A ⊎ B
           → (B → A ⊎ C)
           → A ⊎ C
    _>>=⊎_ q f = flip ([_,_] inj₁) q f
\end{code}
\end{document}
