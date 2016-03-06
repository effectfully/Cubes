module Cubes.Prelude where

open import Function public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base  hiding (_≟_; _⊔_) public
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin) public
open import Data.Maybe.Base hiding (map) public
open import Data.Product hiding (,_) public

open import Level
import Data.Fin.Properties as FinProp
import Data.Maybe as Maybe
open import Category.Monad

private open module Dummy {α} = RawMonad {α} Maybe.monad hiding (pure; zipWith) public

infix 4 ,_
pattern ,_ y = _ , y

infixl 1 _>>=ᵀ_ _>>ᵀ_ _>>=ᵗ_

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set (ι ⊔ α ⊔ β)
A ∸> B = ∀ {i} -> A i -> B i

generalize : ∀ {α β} {A : Set α} {x} -> (B : A -> Set β) -> B x -> ∃ λ x' -> B x' × x ≡ x'
generalize B y = , y , refl

cong₃ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {x₁ x₂ y₁ y₂ z₁ z₂}
      -> (f : A -> B -> C -> D) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> z₁ ≡ z₂ -> f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

cong₄ : ∀ {α β γ δ ε} {A : Set α} {B : Set β} {C : Set γ}
          {D : Set δ} {E : Set ε} {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂}
      -> (f : A -> B -> C -> D -> E)
      -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> z₁ ≡ z₂ -> w₁ ≡ w₂ -> f x₁ y₁ z₁ w₁ ≡ f x₂ y₂ z₂ w₂
cong₄ f refl refl refl refl = refl

revert : ∀ {n} -> Fin n -> ℕ
revert {suc n}  fzero   = n
revert {suc n} (fsuc i) = revert i

_>>=ᵀ_ : ∀ {α β} {A : Set α} -> Maybe A -> (A -> Set β) -> Set β
nothing >>=ᵀ B = Lift ⊤
just x  >>=ᵀ B = B x

_>>ᵀ_ : ∀ {α β} {A : Set α} -> Maybe A -> Set β -> Set β
a >>ᵀ B = a >>=ᵀ λ _ -> B

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β} mx -> (∀ x -> B x) -> mx >>=ᵀ B
nothing >>=ᵗ f = _
just x  >>=ᵗ f = f x

MEquates : ∀ {α} -> Set α -> Set α
MEquates A = (x y : A) -> Maybe (x ≡ y)

FamMEquates : ∀ {α β} {A : Set α} -> (A -> Set β) -> Set (α ⊔ β)
FamMEquates B = ∀ {x} -> MEquates (B x)

record MEq {α} (A : Set α) : Set α where
  infix 5 _≟_ _==_
  field _≟_ : MEquates A

  _==_ : A -> A -> Bool
  x == y = is-just (x ≟ y)
open MEq {{...}} public

FamMEq : ∀ {α β} {A : Set α} -> (A -> Set β) -> Set (α ⊔ β)
FamMEq B = ∀ {x} -> MEq (B x)

instance
  finMEq : FamMEq Fin
  finMEq = record { _≟_ = λ i j -> decToMaybe (i FinProp.≟ j) }
