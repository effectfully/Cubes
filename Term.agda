module Cubes.Term where

open import Cubes.Prelude
open import Cubes.Structures

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
      inv  : Term  n      -> Term  n
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
      go (inv i)        = "inv" |++| go i
      go (var v)        = "var" |++| show v
      go (ƛ b)          = "ƛ" |++ go b
      go (δ x)          = "δ" |++ go x
      go (f · x)        = go f |++| go x
      go (p # i)        = go p |++| go i
      go (coe τ j x)    = "coe" |++ go τ |++ go j |++| go x 

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
      go (inv i₁            ) (inv i₂            ) = cong inv <$> go i₁ i₂
      go (var v₁            ) (var v₂            ) = cong var <$> v₁ ≟ v₂
      go (ƛ b₁              ) (ƛ b₂              ) = cong ƛ_ <$> go b₁ b₂
      go (δ x₁              ) (δ x₂              ) = cong δ_ <$> go x₁ x₂
      go (f₁ · x₁           ) (f₂ · x₂           ) = cong₂ _·_ <$> go f₁ f₂ ⊛ go x₁ x₂
      go (p₁ # i₁           ) (p₂ # i₂           ) = cong₂ _#_ <$> go p₁ p₂ ⊛ go i₁ i₂
      go (coe τ₁ j₁ x₁      ) (coe τ₂ j₂ x₂      ) = cong₃ coe <$> go τ₁ τ₂ ⊛ go j₁ j₂ ⊛ go x₁ x₂
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
      go ι (inv i)        = inv (go ι i)
      go ι (var v)        = var (ren ι v)
      go ι (ƛ b)          = ƛ (go (keep ι) b)
      go ι (δ x)          = δ (go (keep ι) x)
      go ι (f · x)        = go ι f · go ι x
      go ι (p # i)        = go ι p # go ι i
      go ι (coe τ j x)    = coe (go ι τ) (go ι j) (go ι x)

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
      go (inv i)        = inv (go i)
      go (var v)        = var (inject+ _ v)
      go (ƛ b)          = ƛ (go b)
      go (δ x)          = δ (go x)
      go (f · x)        = go f · go x
      go (p # i)        = go p # go i
      go (coe τ j x)    = coe (go τ) (go j) (go x)

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
      go ι (inv i)        = inv <$> go ι i
      go ι (var v)        = var <$> unren ι v
      go ι (ƛ b)          = ƛ_ <$> go (keep ι) b
      go ι (δ x)          = δ_ <$> go (keep ι) x
      go ι (f · x)        = _·_ <$> go ι f ⊛ go ι x
      go ι (p # i)        = _#_ <$> go ι p ⊛ go ι i
      go ι (coe τ j x)    = coe <$> go ι τ ⊛ go ι j ⊛ go ι x
  
    termEnvironment : Environment Term
    termEnvironment = record { fresh = var fzero }

  _⇒_ : ∀ {n} -> Term n -> Term n -> Term n
  σ ⇒ τ = π σ (shift τ)

  showCode : {{aShow : Show A}} -> Fam Shows Term
  showCode t = "`" s++ show t s++ "`"

  Bind : ℕ -> ℕ -> Set
  Bind n  0      = Term n
  Bind n (suc m) = (∀ {p} -> Term (suc n + p)) -> Bind (suc n) m

  instᵇ : ∀ {n m} -> Bind n (suc m) -> Bind (suc n) m
  instᵇ {n} b = b (var (fromℕ⁻ n))

  pi : ∀ {n} -> Term n -> Bind n 1 -> Term n
  pi σ = π σ ∘ instᵇ

  lam : ∀ {n} m -> Bind n m -> Term n
  lam  0      b = b
  lam (suc m) b = ƛ (lam m (instᵇ b))

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
