{-# OPTIONS --no-positivity-check #-}

module Cubes.Core where

open import Cubes.Structures public

infixr 3 ƛ_ δ_
infixl 6 _·_

mutual
  Type = Term

  data Term n : Set where
    int      : Type  n
    type     : Type  n
    π        : Type  n      -> Type (suc n) -> Type n
    path     : Type (suc n) -> Term  n      -> Term n -> Type n
    l r      : Term  n
    var      : Fin   n      -> Term  n
    ƛ_       : Term (suc n) -> Term  n
    δ_       : Term (suc n) -> Term  n
    _·_      : Term  n      -> Term  n      -> Term n
    _#⟨_,_⟩_ : Term  n      -> Term  n      -> Term n -> Term n -> Term n
    coe      : Term (suc n) -> Term  n      -> Term n -> Term n

data Value n : Set
open Kripke Value public
data Value n where
  intᵛ      : Value  n
  typeᵛ     : Value  n
  piᵛ       : Value  n -> Kripke n -> Value n
  pathᵛ     : Kripke n -> Value  n -> Value n -> Value n
  lᵛ rᵛ     : Value  n
  varᵛ      : Fin    n -> Value  n
  lamᵛ      : Kripke n -> Value  n
  dimᵛ      : Kripke n -> Value  n
  _·ᵛ_      : Value  n -> Value  n -> Value n
  _#⟨_,_⟩ᵛ_ : Value  n -> Value  n -> Value n -> Value n -> Value n
  coeᵛ      : Kripke n -> Value  n -> Value n -> Value n

instance
  termMEq : FamMEq Term
  termMEq = record { _≟_ = go } where
    go : FamMEquates Term
    go (int               ) (int               ) = just refl
    go (type              ) (type              ) = just refl
    go (π σ₁ τ₁           ) (π σ₂ τ₂           ) = cong₂ π <$> go σ₁ σ₂ ⊛ go τ₁ τ₂
    go (path σ₁ x₁ y₁     ) (path σ₂ x₂ y₂     ) = cong₃ path <$> go σ₁ σ₂ ⊛ go x₁ x₂ ⊛ go y₁ y₂ 
    go (l                 ) (l                 ) = just refl
    go (r                 ) (r                 ) = just refl
    go (var v₁            ) (var v₂            ) = cong var <$> v₁ ≟ v₂
    go (ƛ b₁              ) (ƛ b₂              ) = cong ƛ_ <$> go b₁ b₂
    go (δ x₁              ) (δ x₂              ) = cong δ_ <$> go x₁ x₂
    go (f₁ · x₁           ) (f₂ · x₂           ) = cong₂ _·_ <$> go f₁ f₂ ⊛ go x₁ x₂
    go (p₁ #⟨ x₁ , y₁ ⟩ i₁) (p₂ #⟨ x₂ , y₂ ⟩ i₂) =
      cong₄ _#⟨_,_⟩_ <$> go p₁ p₂ ⊛ go x₁ x₂ ⊛ go y₁ y₂ ⊛ go i₁ i₂
    go (coe σ₁ x₁ j₁      ) (coe σ₂ x₂ j₂      ) = cong₃ coe <$> go σ₁ σ₂ ⊛ go x₁ x₂ ⊛ go j₁ j₂
    go  _                    _                   = nothing

  finContext : Context Fin
  finContext = record { ren = go } where
    go : Renames Fin
    go  stop     i       = i
    go (skip ι)  i       = fsuc (go ι i)
    go (keep ι)  fzero   = fzero
    go (keep ι) (fsuc i) = fsuc (go ι i)

  termContext : Context Term
  termContext = record { ren = go } where
    go : Renames Term
    go ι  int               = int
    go ι  type              = type
    go ι (π σ τ)            = π (go ι σ) (go (keep ι) τ)
    go ι (path σ x₁ x₂)     = path (go (keep ι) σ) (go ι x₁) (go ι x₂)
    go ι  l                 = l
    go ι  r                 = r
    go ι (var v)            = var (ren ι v)
    go ι (ƛ b)              = ƛ (go (keep ι) b)
    go ι (δ x)              = δ (go (keep ι) x)
    go ι (f · x)            = go ι f · go ι x
    go ι (p #⟨ x₁ , x₂ ⟩ i) = go ι p #⟨ go ι x₁ , go ι x₂ ⟩ go ι i
    go ι (coe σ x j)        = coe (go (keep ι) σ) (go ι x) (go ι j)

  valueContext : Context Value
  valueContext = record { ren = go } where
    go : Renames Value
    go ι  intᵛ               = intᵛ
    go ι  typeᵛ              = typeᵛ
    go ι (piᵛ σ τₖ)          = piᵛ (go ι σ) (renᵏ ι τₖ)
    go ι (pathᵛ σₖ x₁ x₂)    = pathᵛ (renᵏ ι σₖ) (go ι x₁) (go ι x₂)
    go ι  lᵛ                 = lᵛ
    go ι  rᵛ                 = rᵛ
    go ι (varᵛ v)            = varᵛ (ren ι v)
    go ι (lamᵛ bₖ)           = lamᵛ (renᵏ ι bₖ)
    go ι (dimᵛ xₖ)           = dimᵛ (renᵏ ι xₖ)
    go ι (f ·ᵛ x)            = go ι f ·ᵛ go ι x
    go ι (p #⟨ x₁ , x₂ ⟩ᵛ i) = go ι p #⟨ go ι x₁ , go ι x₂ ⟩ᵛ go ι i
    go ι (coeᵛ σₖ x j)       = coeᵛ (renᵏ ι σₖ) (go ι x) (go ι j)

  finBackwards : Backwards Fin
  finBackwards = record { unren = go } where
    go : Unrenames Fin
    go  stop     i       = just i
    go (skip ι)  fzero   = nothing
    go (skip ι) (fsuc i) = go ι i
    go (keep ι)  fzero   = just fzero
    go (keep ι) (fsuc i) = fsuc <$> go ι i

  termBackwards : Backwards Term
  termBackwards = record { unren = go } where
    go : Unrenames Term
    go ι  int               = just int
    go ι  type              = just type
    go ι (π σ τ)            = π <$> go ι σ ⊛ go (keep ι) τ
    go ι (path σ x₁ x₂)     = path <$> go (keep ι) σ ⊛ go ι x₁ ⊛ go ι x₂
    go ι  l                 = just l
    go ι  r                 = just r
    go ι (var v)            = var <$> unren ι v
    go ι (ƛ b)              = ƛ_ <$> go (keep ι) b
    go ι (δ x)              = δ_ <$> go (keep ι) x
    go ι (f · x)            = _·_ <$> go ι f ⊛ go ι x
    go ι (p #⟨ x₁ , x₂ ⟩ i) = _#⟨_,_⟩_ <$> go ι p ⊛ go ι x₁ ⊛ go ι x₂ ⊛ go ι i
    go ι (coe σ x j)        = coe <$> go (keep ι) σ ⊛ go ι x ⊛ go ι j

  finEnvironment   : Environment Fin
  finEnvironment   = record { fresh =      fzero }
  
  termEnvironment  : Environment Term
  termEnvironment  = record { fresh = var  fzero }
  
  valueEnvironment : Environment Value
  valueEnvironment = record { fresh = varᵛ fzero }
