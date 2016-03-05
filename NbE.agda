{-# OPTIONS --no-termination-check #-}

module Cubes.NbE where

open import Cubes.Core

infixl 8 _[_]ᵛ _⟦_⟧ᵛ _⟦_⟧ᵏ _[_]

ηƛ : ∀ {n} -> Term (suc n) -> Term n
ηƛ b = case b of λ
  { (f · var fzero) -> maybe′ id (ƛ b) (unshift f)
  ;  _              -> ƛ b
  }

-- Is it safe to ignore `x₁' and `x₂'?
-- Even if it is, throwing `x₁' and `x₂' away allows them to be ill-typed, which is silly.
-- Do we need to define normalization mutually with type checking?
ηδ : ∀ {n} -> Term (suc n) -> Term n
ηδ b = case b of λ
  { (p #⟨ x₁ , x₂ ⟩ var fzero) -> maybe′ id (δ b) (unshift p)
  ;  _                         -> δ b
  }

mutual
  quoteᵛ : Value ∸> Term
  quoteᵛ  intᵛ               = int
  quoteᵛ  typeᵛ              = type
  quoteᵛ (piᵛ σ τₖ)          = π (quoteᵛ σ) (quoteᵏ τₖ)
  quoteᵛ (pathᵛ σₖ x₁ x₂)    = path (quoteᵏ σₖ) (quoteᵛ x₁) (quoteᵛ x₂)
  quoteᵛ  lᵛ                 = l
  quoteᵛ  rᵛ                 = r
  quoteᵛ (varᵛ v)            = var v
  quoteᵛ (lamᵛ bₖ)           = ηƛ (quoteᵏ bₖ)
  quoteᵛ (dimᵛ xₖ)           = ηδ (quoteᵏ xₖ)
  quoteᵛ (f ·ᵛ x)            = quoteᵛ f · quoteᵛ x
  quoteᵛ (p #⟨ x₁ , x₂ ⟩ᵛ i) = quoteᵛ p #⟨ quoteᵛ x₁ , quoteᵛ x₂ ⟩ quoteᵛ i
  quoteᵛ (coeᵛ Aₖ x j)       = coe (quoteᵏ Aₖ) (quoteᵛ x) (quoteᵛ j)

  quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
  quoteᵏ = quoteᵛ ∘ instᵏ

isShiftable : ∀ {n} -> Term (suc n) -> Bool
isShiftable = is-just ∘ unshift

isShiftableᵛ : ∀ {n} -> Value (suc n) -> Bool
isShiftableᵛ = isShiftable ∘ quoteᵛ

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ k $ᵛ x = k [ x ]ᵏ
f      $ᵛ x = f ·ᵛ x

_$⟨_,_⟩ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n -> Value n -> Value n
p      $⟨ x₁ , x₂ ⟩ᵛ lᵛ = x₁
p      $⟨ x₁ , x₂ ⟩ᵛ rᵛ = x₂
dimᵛ k $⟨ x₁ , x₂ ⟩ᵛ i  = k [ i ]ᵏ
p      $⟨ x₁ , x₂ ⟩ᵛ i  = p #⟨ x₁ , x₂ ⟩ᵛ i

mutual
  ⟦_/_⟧ᵛ : ∀ {n m} -> m ↤ n -> Term n -> Value m
  ⟦ ρ / int              ⟧ᵛ = intᵛ
  ⟦ ρ / type             ⟧ᵛ = typeᵛ
  ⟦ ρ / π σ τ            ⟧ᵛ = piᵛ ⟦ ρ / σ ⟧ᵛ ⟦ ρ / τ ⟧ᵏ
  ⟦ ρ / path A x₁ x₂     ⟧ᵛ = pathᵛ ⟦ ρ / A ⟧ᵏ ⟦ ρ / x₁ ⟧ᵛ ⟦ ρ / x₂ ⟧ᵛ
  ⟦ ρ / l                ⟧ᵛ = lᵛ
  ⟦ ρ / r                ⟧ᵛ = rᵛ
  ⟦ ρ / var v            ⟧ᵛ = lookupᵉ v ρ
  ⟦ ρ / ƛ b              ⟧ᵛ = lamᵛ ⟦ ρ / b ⟧ᵏ
  ⟦ ρ / δ x              ⟧ᵛ = dimᵛ ⟦ ρ / x ⟧ᵏ
  ⟦ ρ / f · x            ⟧ᵛ = ⟦ ρ / f ⟧ᵛ $ᵛ ⟦ ρ / x ⟧ᵛ 
  ⟦ ρ / p #⟨ x₁ , x₂ ⟩ i ⟧ᵛ = ⟦ ρ / p ⟧ᵛ $⟨ ⟦ ρ / x₁ ⟧ᵛ , ⟦ ρ / x₂ ⟧ᵛ ⟩ᵛ ⟦ ρ / i ⟧ᵛ
  ⟦ ρ / coe σ x j        ⟧ᵛ = case ⟦j⟧ of λ
    { lᵛ -> ⟦x⟧
    ; _  -> if isShiftableᵛ ⟦ keepᵉ ρ / σ ⟧ᵛ then ⟦x⟧ else coeᵛ ⟦ ρ / σ ⟧ᵏ ⟦x⟧ ⟦j⟧
    } where ⟦x⟧ = ⟦ ρ / x ⟧ᵛ; ⟦j⟧ = ⟦ ρ / j ⟧ᵛ

  ⟦_/_⟧ᵏ : ∀ {n m} -> m ↤ n -> Term (suc n) -> Kripke m
  ⟦ ρ / b ⟧ᵏ ι x = ⟦ renᵉ ι ρ ▷ x / b ⟧ᵛ

eval : Term ∸> Value
eval = ⟦ stopᵉ /_⟧ᵛ

norm : Term ∸> Term
norm = quoteᵛ ∘ eval

-- _⟦_⟧ᵏ : ∀ {n} -> Kripke n -> Term n -> Value n
-- k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

⟦_⟧[_] : ∀ {n} -> Term (suc n) -> Value n -> Value n
⟦ b ⟧[ x ] = ⟦ stopᵉ ▷ x / b ⟧ᵛ

⟦_⟧⟦_⟧ : ∀ {n} -> Term (suc n) -> Term n -> Value n
⟦ b ⟧⟦ x ⟧ = ⟦ b ⟧[ eval x ]

_[_]ᵛ : ∀ {n} -> Value (suc n) -> Value n -> Value n
b [ x ]ᵛ = ⟦ quoteᵛ b ⟧[ x ]

_⟦_⟧ᵛ : ∀ {n} -> Value (suc n) -> Term n -> Value n
b ⟦ x ⟧ᵛ = b [ eval x ]ᵛ

_⟦_⟧ᵏ : ∀ {n} -> Kripke n -> Term n -> Value n
k ⟦ x ⟧ᵏ = instᵏ k ⟦ x ⟧ᵛ

abstᵏ : ∀ {n} -> Value (suc n) -> Kripke n
abstᵏ b ι x = ren (keep ι) b [ x ]ᵛ

-- ⟦_⟧⟦_⟧ : ∀ {n} -> Term (suc n) -> Term n -> Value n
-- ⟦ b ⟧⟦ x ⟧ = abstᵏ (eval b) ⟦ x ⟧ᵏ

_[_] : ∀ {n} -> Term (suc n) -> Term n -> Term n
b [ x ] = quoteᵛ ⟦ b ⟧⟦ x ⟧
