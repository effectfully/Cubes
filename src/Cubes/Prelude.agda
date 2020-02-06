module Cubes.Prelude where

open import Function         using (_$_; _∘_; const; flip; id; case_of_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂) public
open import Data.Empty       using (⊥; ⊥-elim) public
open import Data.Unit.Base   using (⊤; tt) public
open import Data.Bool.Base   using (Bool; true; false; if_then_else_; not; _∧_; _∨_) public
open import Data.Nat.Base    using (ℕ; zero; suc; _+_) public
open import Data.Fin         using (Fin; toℕ; inject+) renaming (zero to fzero; suc to fsuc) public
open import Data.String.Base using (String; toList) renaming (_++_ to _s++_) public
open import Data.Maybe.Base  using (Maybe; nothing; just; maybe′; is-just; decToMaybe) public
open import Data.Sum         using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map to smap) public
open import Data.Product     using (Σ; ∃; _×_; _,_; proj₁; proj₂) public
open import Data.List.Base   using (List; foldr; map; any; intersperse) public
open import Data.Vec         using (Vec; []; _∷_; lookup) renaming (map to vmap) public

open import Level hiding (zero; suc)
open import Data.Char as Char using (Char)
open import Data.Fin using (inject₁; fromℕ)
import Data.Nat.Show as NatShow
import Data.Fin.Properties as FinProp
import Data.Maybe as Maybe
open import Category.Monad

open RawMonad {{...}} hiding (pure; zipWith) public

infix  4 ,_
infix  4 _∈?_
infixr 5 _|++_ _|++|_

pattern ,_ y = _ , y

_∸>_ : ∀ {ι α β} {I : Set ι} -> (I -> Set α) -> (I -> Set β) -> Set (ι ⊔ α ⊔ β)
A ∸> B = ∀ {i} -> A i -> B i

Shows : ∀ {α} -> Set α -> Set α
Shows A = A -> String

record Show {α} (A : Set α) : Set α where
  field show : Shows A
open Show {{...}} public

Fam : ∀ {α β γ} {A : Set α} {B : A -> Set β}
    -> (∀ {x} -> B x -> Set γ) -> (∀ x -> B x) -> Set (α ⊔ γ)
Fam F f = ∀ {x} -> F (f x)

instance
  ⊥Show : Show ⊥
  ⊥Show = record { show = const "" }

  natShow : Show ℕ
  natShow = record { show = NatShow.show }

  finShow : Fam Show Fin
  finShow = record { show = show ∘ toℕ }

  maybeMonad : ∀ {α} -> RawMonad {α} Maybe
  maybeMonad = record
    { return = just
    ; _>>=_  = Maybe._>>=_
    }

  sumMonad : ∀ {α β} {A : Set α} -> RawMonad {α ⊔ β} (A ⊎_)
  sumMonad = record
    { return = inj₂
    ; _>>=_  = λ s f -> [ inj₁ , f ]′ s
    }

maybeToSum : ∀ {α β} {A : Set α} {B : Set β} -> A -> Maybe B -> A ⊎ B
maybeToSum = maybe′ inj₂ ∘ inj₁

MEquates : ∀ {α} -> Set α -> Set α
MEquates A = (x y : A) -> Maybe (x ≡ y)

record MEq {α} (A : Set α) : Set α where
  infix 7 _≟_ _==_
  field _≟_ : MEquates A

  _==_ : A -> A -> Bool
  x == y = is-just (x ≟ y)
open MEq {{...}} public

instance
  ⊥MEq : MEq ⊥
  ⊥MEq = record { _≟_ = λ() }

  charMEq : MEq Char
  charMEq = record { _≟_ = λ c d -> decToMaybe (c Char.≟ d) }

  finMEq : Fam MEq Fin
  finMEq = record { _≟_ = λ i j -> decToMaybe (i FinProp.≟ j) }

_∈?_ : ∀ {α} {A : Set α} {{aMEq : MEq A}} -> A -> List A -> Bool
_∈?_ x = any (_== x)

sconcat : List String -> String
sconcat = foldr (_s++_) ""

unwords : List String -> String
unwords = sconcat ∘ intersperse " "

parens : String -> String
parens s = if ' ' ∈? toList s then "(" s++ s s++ ")" else s

_|++_ : String -> String -> String
s₁ |++ s₂ = parens s₁ s++ " " s++ s₂

_|++|_ : String -> String -> String
s₁ |++| s₂ = s₁ |++ parens s₂

generalize : ∀ {α β} {A : Set α} {x} -> (B : A -> Set β) -> B x -> ∃ λ x' -> B x' × x ≡ x'
generalize B y = , y , refl

left : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} -> (A -> C) -> A ⊎ B -> C ⊎ B
left f = smap f id

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

module _ {α β} {A : Set α} {B : Set β} where
  infixl 1 _>>=ᵀ_ _>>=ᵗ_

  _>>=ᵀ_ : A ⊎ B -> (B -> Set α) -> Set α
  inj₁ x >>=ᵀ C = A
  inj₂ y >>=ᵀ C = C y

  _>>=ᵗ_ : ∀ {C} s -> (∀ y -> C y) -> s >>=ᵀ C
  inj₁ x >>=ᵗ g = x
  inj₂ y >>=ᵗ g = g y
