{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- Everything is terminating if you replace (instᵏ k) with (k top fresh).

module Cubes.Core where

open import Cubes.Structures public

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
    go ι (varᵛ v)        = varᵛ (ren ι v)
    go ι (lamᵛ bₖ)       = lamᵛ (renᵏ ι bₖ)
    go ι (dimᵛ xₖ)       = dimᵛ (renᵏ ι xₖ)
    go ι (f ·ᵛ x)        = go ι f ·ᵛ go ι x
    go ι (p #ᵛ i)        = go ι p #ᵛ go ι i
    go ι (coeᵛ σ j x)    = coeᵛ (go ι σ) (go ι j) (go ι x)

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
    go (lamᵛ bₖ)       = lamᵛ (wkᵏ bₖ)
    go (dimᵛ xₖ)       = dimᵛ (wkᵏ xₖ)
    go (f ·ᵛ x)        = go f ·ᵛ go x
    go (p #ᵛ i)        = go p #ᵛ go i
    go (coeᵛ σ j x)    = coeᵛ (go σ) (go j) (go x)

  valueEnvironment : Environment Value
  valueEnvironment = record { fresh = varᵛ fzero }

  valueSubstitution : Substitution Value
  valueSubstitution = record { sub = go } where
    mutual
      go : Substitutes Value Value
      go ρ  intᵛ           = intᵛ
      go ρ  typeᵛ          = typeᵛ
      go ρ (piᵛ σ τₖ)      = piᵛ (go ρ σ) (goᵏ ρ τₖ)
      go ρ (pathᵛ σ x₁ x₂) = pathᵛ (go ρ σ) (go ρ x₁) (go ρ x₂)
      go ρ  lᵛ             = lᵛ
      go ρ  rᵛ             = rᵛ
      go ρ (varᵛ v)        = lookupᵉ v ρ
      go ρ (lamᵛ bₖ)       = lamᵛ (goᵏ ρ bₖ)
      go ρ (dimᵛ xₖ)       = dimᵛ (goᵏ ρ xₖ)
      go ρ (f ·ᵛ x)        = go ρ f ·ᵛ go ρ x
      go ρ (p #ᵛ i)        = go ρ p #ᵛ go ρ i
      go ρ (coeᵛ σ j x)    = coeᵛ (go ρ σ) (go ρ j) (go ρ x)

      goᵏ : Substitutes Kripke Value
      goᵏ ρ k ι x = go (renᵉ ι ρ ▷ x) (instᵏ k)

_⇒ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
σ ⇒ᵛ τ = piᵛ σ (λ ι _ -> ren ι τ)

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ k $ᵛ x = k [ x ]ᵏ
f      $ᵛ x = f ·ᵛ x

abstᵏ : ∀ {n} -> Value (suc n) -> Kripke n
abstᵏ b ι x = ren (keep ι) b [ x ]

ƛᵛ : ∀ {n} -> Value (suc n) -> Value n
ƛᵛ = lamᵛ ∘ abstᵏ

module TermWith A where
  infixr 3 ƛ_ δ_
  infixl 6 _·_ _#_

  mutual
    Type = Term

    data Term n : Set where
      pure : A -> Term n
      int  : Type  n
      type : Type  n
      π    : Type  n      -> Type (suc n) -> Type n
      path : Type  n      -> Term  n      -> Term n -> Type n
      l r  : Term  n
      var  : Fin   n      -> Term  n
      ƛ_   : Term (suc n) -> Term  n
      δ_   : Term (suc n) -> Term  n
      _·_  : Term  n      -> Term  n      -> Term n
      _#_  : Term  n      -> Term  n      -> Term n
      coe  : Term  n      -> Term  n      -> Term n -> Term n

  Term⁽⁾ : Set
  Term⁽⁾ = Term 0

  Term⁺ : Set
  Term⁺ = ∀ {n} -> Term n
  
  Type⁽⁾ = Term⁽⁾
  Type⁺  = Term⁺

open TermWith ⊥ renaming (Term to Pure) using () public

module _ {A} where
  open TermWith A

  infixr 5 _⇒_

  instance
    termShow : {{aShow : Show A}} -> Fam Show Term
    termShow = record { show = go } where
      go : Fam Shows Term
      go (pure x)       = show x
      go  int           = "int"
      go  type          = "type"
      go (π σ τ)        = "π" |++ go σ |++| go τ
      go (path σ x₁ x₂) = "path" |++ go σ |++ go x₁ |++| go x₂
      go  l             = "l"
      go  r             = "r"
      go (var v)        = "var" |++| show v
      go (ƛ b)          = "ƛ" |++ go b
      go (δ x)          = "δ" |++ go x
      go (f · x)        = go f |++| go x
      go (p # i)        = go p |++| go i
      go (coe σ j x)    = "coe" |++ go σ |++ go j |++| go x 

    termMEq : {{aMEq : MEq A}} -> Fam MEq Term
    termMEq = record { _≟_ = go } where
      go : Fam MEquates Term
      go (pure x₁           ) (pure x₂           ) = cong pure <$> x₁ ≟ x₂
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
      go (p₁ # i₁           ) (p₂ # i₂           ) = cong₂ _#_ <$> go p₁ p₂ ⊛ go i₁ i₂
      go (coe σ₁ j₁ x₁      ) (coe σ₂ j₂ x₂      ) = cong₃ coe <$> go σ₁ σ₂ ⊛ go j₁ j₂ ⊛ go x₁ x₂
      go  _                    _                   = nothing

    termContext : Context Term
    termContext = record { ren = go } where
      go : Renames Term
      go ι (pure x)       = pure x
      go ι  int           = int
      go ι  type          = type
      go ι (π σ τ)        = π (go ι σ) (go (keep ι) τ)
      go ι (path σ x₁ x₂) = path (go ι σ) (go ι x₁) (go ι x₂)
      go ι  l             = l
      go ι  r             = r
      go ι (var v)        = var (ren ι v)
      go ι (ƛ b)          = ƛ (go (keep ι) b)
      go ι (δ x)          = δ (go (keep ι) x)
      go ι (f · x)        = go ι f · go ι x
      go ι (p # i)        = go ι p # go ι i
      go ι (coe σ j x)    = coe (go ι σ) (go ι j) (go ι x)

    termAppend : Append Term
    termAppend = record { wk = go } where
      go : ∀ {n m} -> Term n -> Term (n + m)
      go (pure x)       = pure x
      go  int           = int
      go  type          = type
      go (π σ τ)        = π (go σ) (go τ)
      go (path σ x₁ x₂) = path (go σ) (go x₁) (go x₂)
      go  l             = l
      go  r             = r
      go (var v)        = var (inject+ _ v)
      go (ƛ b)          = ƛ (go b)
      go (δ x)          = δ (go x)
      go (f · x)        = go f · go x
      go (p # i)        = go p # go i
      go (coe σ j x)    = coe (go σ) (go j) (go x)

    termBackwards : Backwards Term
    termBackwards = record { unren = go } where
      go : Unrenames Term
      go ι (pure x)       = just (pure x)
      go ι  int           = just int
      go ι  type          = just type
      go ι (π σ τ)        = π <$> go ι σ ⊛ go (keep ι) τ
      go ι (path σ x₁ x₂) = path <$> go ι σ ⊛ go ι x₁ ⊛ go ι x₂
      go ι  l             = just l
      go ι  r             = just r
      go ι (var v)        = var <$> unren ι v
      go ι (ƛ b)          = ƛ_ <$> go (keep ι) b
      go ι (δ x)          = δ_ <$> go (keep ι) x
      go ι (f · x)        = _·_ <$> go ι f ⊛ go ι x
      go ι (p # i)        = _#_ <$> go ι p ⊛ go ι i
      go ι (coe σ j x)    = coe <$> go ι σ ⊛ go ι j ⊛ go ι x
  
    termEnvironment : Environment Term
    termEnvironment = record { fresh = var fzero }

  _⇒_ : ∀ {n} -> Term n -> Term n -> Term n
  σ ⇒ τ = π σ (shift τ)

  isShiftable : ∀ {n} -> Term (suc n) -> Bool
  isShiftable = is-just ∘ unshift

  showCode : {{aShow : Show A}} -> Fam Shows Term
  showCode t = "`" s++ show t s++ "`"

  Bind : ℕ -> ℕ -> Set
  Bind n  0      = Term n
  Bind n (suc m) = (∀ {p} -> Term (suc n + p)) -> Bind (suc n) m

  instᵇ : ∀ {n m} -> Bind n (suc m) -> Bind (suc n) m
  instᵇ {n} b = b (var (fromℕ⁻ n))

  pi : ∀ {n} -> Term n -> Bind n 1 -> Term n
  pi {n} σ b = π σ (instᵇ b)

  lam : ∀ {n} m -> Bind n m -> Term n
  lam      zero   b = b
  lam {n} (suc m) b = ƛ (lam m (instᵇ b))

  dim : ∀ {n} -> Bind n 1 -> Term n
  dim = δ_ ∘ instᵇ

  ηƛ : ∀ {n} -> Term (suc n) -> Term n
  ηƛ b = case b of λ
    { (f · var fzero) -> maybe′ id (ƛ b) (unshift f)
    ;  _              -> ƛ b
    }

  ηδ : ∀ {n} -> Term (suc n) -> Term n
  ηδ b = case b of λ
    { (p # var fzero) -> maybe′ id (δ b) (unshift p)
    ;  _              -> δ b
    }

  mutual
    quoteᵛ : Value ∸> Term
    quoteᵛ  intᵛ           = int
    quoteᵛ  typeᵛ          = type
    quoteᵛ (piᵛ σ τₖ)      = π (quoteᵛ σ) (quoteᵏ τₖ)
    quoteᵛ (pathᵛ σ x₁ x₂) = path (quoteᵛ σ) (quoteᵛ x₁) (quoteᵛ x₂)
    quoteᵛ  lᵛ             = l
    quoteᵛ  rᵛ             = r
    quoteᵛ (varᵛ v)        = var v
    quoteᵛ (lamᵛ bₖ)       = ηƛ (quoteᵏ bₖ)
    quoteᵛ (dimᵛ xₖ)       = ηδ (quoteᵏ xₖ)
    quoteᵛ (f ·ᵛ x)        = quoteᵛ f · quoteᵛ x
    quoteᵛ (p #ᵛ i)        = quoteᵛ p # quoteᵛ i
    quoteᵛ (coeᵛ σ x j)    = coe (quoteᵛ σ) (quoteᵛ x) (quoteᵛ j)

    -- Expanding (quoteᵛ ∘ instᵏ) to satisfy the termination checker.
    quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
    quoteᵏ k = quoteᵛ (instᵏ k)

quoteᵛ₀ : Value ∸> Pure
quoteᵛ₀ = quoteᵛ

isShiftableᵛ : ∀ {n} -> Value (suc n) -> Bool
isShiftableᵛ = isShiftable ∘ quoteᵛ₀

isConstᵛ : ∀ {n} -> Value n -> Bool
isConstᵛ (lamᵛ b) = isShiftableᵛ (instᵏ b)
isConstᵛ  _       = false
