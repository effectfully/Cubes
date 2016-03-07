module Cubes.Prelude where

open import Function public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base  hiding (_≟_; _⊔_) public
open import Data.Fin renaming (zero to fzero; suc to fsuc) using (Fin; inject+) public
open import Data.Maybe.Base hiding (map) public
open import Data.Product hiding (,_) public

open import Level hiding (zero; suc)
open import Data.Fin using (inject₁; fromℕ)
import Data.Fin.Properties as FinProp
import Data.Maybe as Maybe
open import Category.Monad

private open module Dummy {α} = RawMonad {α} Maybe.monad hiding (pure; zipWith) public

infix 4 ,_
pattern ,_ y = _ , y

infixl 1 _>>=ᵀ_ _>>=ᵗ_

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

fromℕ⁻ : ∀ {m} n -> Fin (suc n + m)
fromℕ⁻  0      = fromℕ _
fromℕ⁻ (suc n) = inject₁ (fromℕ⁻ n)

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

data _>>=ᵀ_ {α β} {A : Set α} : (a : Maybe A) -> (A -> Set β) -> Set β where
  nothingᵗ : ∀ {B}   ->        nothing >>=ᵀ B
  justᵗ    : ∀ {x B} -> B x -> just x  >>=ᵀ B

_>>=ᵗ_ : ∀ {α β} {A : Set α} {B : A -> Set β}
       -> (a : Maybe A) -> (∀ x -> B x) -> a >>=ᵀ B
nothing >>=ᵗ f = nothingᵗ
just  x >>=ᵗ f = justᵗ (f x)

recᵗ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {a : Maybe A}
      -> (∀ {x} -> B x -> C) -> C -> a >>=ᵀ B -> C
recᵗ g z  nothingᵗ = z
recᵗ g z (justᵗ y) = g y

FromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : A -> Set β}
          -> mx >>=ᵀ B -> Set β
FromJustᵗ  nothingᵗ         = Lift ⊤
FromJustᵗ (justᵗ {x} {B} y) = B x

fromJustᵗ : ∀ {α β} {A : Set α} {mx : Maybe A} {B : A -> Set β}
          -> (yᵗ : mx >>=ᵀ B) -> FromJustᵗ yᵗ
fromJustᵗ  nothingᵗ = _
fromJustᵗ (justᵗ y) = y

_>>=⊤_ : ∀ {α β} {A : Set α} {B : A -> Set β}
       -> (mx : Maybe A) -> (g : ∀ x -> B x) -> FromJustᵗ (mx >>=ᵗ g)
mx >>=⊤ g = fromJustᵗ $ mx >>=ᵗ g
