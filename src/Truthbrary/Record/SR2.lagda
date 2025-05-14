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
open import Function
  using (
    _∘_;
    _$_
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
  using (
    Is-nothing;
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Data.Product
  using (
    _×_
  )
open import Relation.Unary
  using (
    Decidable;
    _⊆_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Relation.Nullary.Decidable
  using (
    from-yes
  )
open import Data.List.Relation.Unary.All
  as 𝕃All
  using (
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

module apDec where
  apDec' : ∀ {a b p}
         → {A : Set a} → {B : Set b}
         → {P : A → Set p}
         → (f : (x : A) → P x → B)
         → (x : A)
         → Dec $ P x
         → Maybe B
  apDec' f x (yes p) = just $ f x p
  apDec' _ _ _ = nothing

  apDec : ∀ {a b p}
        → {A : Set a} → {B : Set b}
        → {P : A → Set p}
        → (f : (x : A) → P x → B)
        → (P? : Decidable P)
        → A
        → Maybe B
  apDec f P? x = apDec' f x $ P? x

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

  field
    justys : P ⊆ (Is-just ∘ readMaybe)
    nad : (¬_ ∘ P) ⊆ (Is-nothing ∘ readMaybe)

module readNat where
    IsDigit : Char → Set
    djm0 : Strong → Set
    djm0 n = 𝕃All.All IsDigit n
    toFin10 : Char → Maybe $ Fin 10
    toFin10 '0' = just 𝔽.zero
    toFin10 '1' = just $ 𝔽.fromℕ< $ from-yes $ 1 ℕ.<? 10
    toFin10 '2' = just $ 𝔽.fromℕ< $ from-yes $ 2 ℕ.<? 10
    toFin10 '3' = just $ 𝔽.fromℕ< $ from-yes $ 3 ℕ.<? 10
    toFin10 '4' = just $ 𝔽.fromℕ< $ from-yes $ 4 ℕ.<? 10
    toFin10 '5' = just $ 𝔽.fromℕ< $ from-yes $ 5 ℕ.<? 10
    toFin10 '6' = just $ 𝔽.fromℕ< $ from-yes $ 6 ℕ.<? 10
    toFin10 '7' = just $ 𝔽.fromℕ< $ from-yes $ 7 ℕ.<? 10
    toFin10 '8' = just $ 𝔽.fromℕ< $ from-yes $ 8 ℕ.<? 10
    toFin10 '9' = just $ 𝔽.fromℕ< $ from-yes $ 9 ℕ.<? 10
    toFin10 _ = nothing
    IsDigit = λ x → Is-just $ toFin10 x
    read : (x : Strong) → djm0 x → ℕ
    read x p = Data.Product.proj₁ $ read' x p
      where
      read' : (x : Strong) → djm0 x → ℕ × ℕ
      read' [] p = 0 Data.Product., 0
      read' (c ∷ cs) (p 𝕃All.∷ ps) =
        n ℕ.+ cℕ ℕ.* 10 ℕ.^ e Data.Product., ℕ.suc e
        where
        n = Data.Product.proj₁ $ read' cs ps
        e = Data.Product.proj₂ $ read' cs ps
        cℕ = 𝔽.toℕ $ Data.Maybe.to-witness p

instance
  readNat : Read {p = Level.zero} ℕ
  readNat = record {
    P = djm0;
    read = read
    }
    where
    open readNat

  readMaybeNat : ReadMaybe ℕ
  readMaybeNat = record {
    rr = readNat;
    P? = {!!};
    justys = {!!};
    nad = {!!}}
\end{code}
