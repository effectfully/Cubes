{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- Everything is terminating if you replace (instᵏ k) with (k top fresh).

module Cubes.Value where

open import Cubes.Prelude
open import Cubes.Structures
open import Cubes.Term

infixl 6 _·ᵛ_ _#ᵛ_ _$ᵛ_
infixr 5 _⇒ᵛ_

data Value n : Set
open Kripke Value public
data Value n where
  intᵛ  : Value  n
  typeᵛ : Value  n
  piᵛ   : Value  n -> Kripke n -> Value n
  pathᵛ : Value  n -> Value  n -> Value n -> Value n
  lᵛ rᵛ : Value  n
  invᵛ  : Value  n -> Value  n
  varᵛ  : Fin    n -> Value  n
  lamᵛ  : Kripke n -> Value  n
  dimᵛ  : Kripke n -> Value  n
  _·ᵛ_  : Value  n -> Value  n -> Value n
  _#ᵛ_  : Value  n -> Value  n -> Value n
  coeᵛ  : Value  n -> Value  n -> Value n -> Value n

Value⁽⁾ : Set
Value⁽⁾ = Value 0

Value⁺ : Set
Value⁺ = ∀ {n} -> Value n

instance
  valueContext : Context Value
  valueContext = record { ren = go } where
    go : Renames Value
    go ι  intᵛ           = intᵛ
    go ι  typeᵛ          = typeᵛ
    go ι (piᵛ σ τₖ)      = piᵛ (go ι σ) (renᵏ ι τₖ)
    go ι (pathᵛ σ x₁ x₂) = pathᵛ (go ι σ) (go ι x₁) (go ι x₂)
    go ι  lᵛ             = lᵛ
    go ι  rᵛ             = rᵛ
    go ι (invᵛ i)        = invᵛ (go ι i)
    go ι (varᵛ v)        = varᵛ (ren ι v)
    go ι (lamᵛ bₖ)       = lamᵛ (renᵏ ι bₖ)
    go ι (dimᵛ xₖ)       = dimᵛ (renᵏ ι xₖ)
    go ι (f ·ᵛ x)        = go ι f ·ᵛ go ι x
    go ι (p #ᵛ i)        = go ι p #ᵛ go ι i
    go ι (coeᵛ τ j x)    = coeᵛ (go ι τ) (go ι j) (go ι x)

  valueAppend : Append Value
  valueAppend = record { wk = go } where
    go : Weakens Value
    go  intᵛ           = intᵛ
    go  typeᵛ          = typeᵛ
    go (piᵛ σ τₖ)      = piᵛ (go σ) (wkᵏ τₖ)
    go (pathᵛ σ x₁ x₂) = pathᵛ (go σ) (go x₁) (go x₂)
    go  lᵛ             = lᵛ
    go  rᵛ             = rᵛ
    go (varᵛ v)        = varᵛ (inject+ _ v)
    go (invᵛ i)        = invᵛ (go i)
    go (lamᵛ bₖ)       = lamᵛ (wkᵏ bₖ)
    go (dimᵛ xₖ)       = dimᵛ (wkᵏ xₖ)
    go (f ·ᵛ x)        = go f ·ᵛ go x
    go (p #ᵛ i)        = go p #ᵛ go i
    go (coeᵛ τ j x)    = coeᵛ (go τ) (go j) (go x)

  valueEnvironment : Environment Value
  valueEnvironment = record { fresh = varᵛ fzero }

     -- Substitution must be normalizing. But it can't be, because of the _#ᵛ_ case,
     -- which needs types in order to compute. But substitution is not used anywhere anyway.
--   valueSubstitution : Substitution Value
--   valueSubstitution = record { sub = go } where
--     mutual
--       go : Substitutes Value Value
--       go ρ  intᵛ           = intᵛ
--       go ρ  typeᵛ          = typeᵛ
--       go ρ (piᵛ σ τₖ)      = piᵛ (go ρ σ) (goᵏ ρ τₖ)
--       go ρ (pathᵛ σ x₁ x₂) = pathᵛ (go ρ σ) (go ρ x₁) (go ρ x₂)
--       go ρ  lᵛ             = lᵛ
--       go ρ  rᵛ             = rᵛ
--       go ρ (invᵛ i)        = invᵛ (go ρ i)
--       go ρ (varᵛ v)        = lookupᵉ v ρ
--       go ρ (lamᵛ bₖ)       = lamᵛ (goᵏ ρ bₖ)
--       go ρ (dimᵛ xₖ)       = dimᵛ (goᵏ ρ xₖ)
--       go ρ (f ·ᵛ x)        = go ρ f ·ᵛ go ρ x
--       go ρ (p #ᵛ i)        = go ρ p #ᵛ go ρ i
--       go ρ (coeᵛ τ j x)    = coeᵛ (go ρ τ) (go ρ j) (go ρ x)

--       goᵏ : Substitutes Kripke Value
--       goᵏ ρ k ι x = go (renᵉ ι ρ ▷ x) (instᵏ k)

-- ƛᵛ : ∀ {n} -> Value (suc n) -> Value n
-- ƛᵛ = lamᵛ ∘ abstᵏ

_⇒ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
σ ⇒ᵛ τ = piᵛ σ (λ ι _ -> ren ι τ)

invertᵛ : ∀ {n} -> Value n -> Value n
invertᵛ  lᵛ      = rᵛ
invertᵛ  rᵛ      = lᵛ
invertᵛ (invᵛ i) = i
invertᵛ  i       = invᵛ i

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ k $ᵛ x = k [ x ]ᵏ
f      $ᵛ x = f ·ᵛ x

module _ {A} where
  open TermWith A

  mutual
    quoteᵛ : Value ∸> Term
    quoteᵛ  intᵛ           = int
    quoteᵛ  typeᵛ          = type
    quoteᵛ (piᵛ σ τₖ)      = π (quoteᵛ σ) (quoteᵏ τₖ)
    quoteᵛ (pathᵛ σ x₁ x₂) = path (quoteᵛ σ) (quoteᵛ x₁) (quoteᵛ x₂)
    quoteᵛ  lᵛ             = l
    quoteᵛ  rᵛ             = r
    quoteᵛ (invᵛ i)        = inv (quoteᵛ i)
    quoteᵛ (varᵛ v)        = var v
    quoteᵛ (lamᵛ bₖ)       = ηƛ (quoteᵏ bₖ)
    quoteᵛ (dimᵛ xₖ)       = ηδ (quoteᵏ xₖ)
    quoteᵛ (f ·ᵛ x)        = quoteᵛ f · quoteᵛ x
    quoteᵛ (p #ᵛ i)        = quoteᵛ p # quoteᵛ i
    quoteᵛ (coeᵛ τ x j)    = coe (quoteᵛ τ) (quoteᵛ x) (quoteᵛ j)

    quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
    quoteᵏ = quoteᵛ ∘ instᵏ

quoteᵛ₀ : Value ∸> Pure
quoteᵛ₀ = quoteᵛ

isUnshiftableᵛ : ∀ {n} -> Value (suc n) -> Bool
isUnshiftableᵛ = isUnshiftable ∘ quoteᵛ₀

isConstᵛ : ∀ {n} -> Value n -> Bool
isConstᵛ (lamᵛ b) = isUnshiftableᵛ (instᵏ b)
isConstᵛ  _       = false

coerceᵛ : ∀ {n} -> Value n -> Value n -> Value n -> Value n
coerceᵛ τ j x = if quoteᵛ j == Pure.l ∨ isConstᵛ τ then x else coeᵛ τ j x
