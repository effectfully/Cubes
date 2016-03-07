{-# OPTIONS --no-termination-check #-}

module Cubes.Typecheck where

open import Cubes.Core

infix  4 _⊢_∈_
infixl 8 _⟦_⟧ᵏ
infix  1 _∈_

mutual
  data _⊢_∈_ {n} (Γ : Con n) : Term n -> Value n -> Set where
    intᵗ     : Γ ⊢ int  ∈ typeᵛ
    typeᵗ    : Γ ⊢ type ∈ typeᵛ
    πᵗ       : ∀ {σ τ}
             -> (σₜ : Γ           ⊢ σ     ∈ typeᵛ)
             ->       Γ ▻ eval σₜ ⊢ τ     ∈ typeᵛ
             ->       Γ           ⊢ π σ τ ∈ typeᵛ
    pathᵗ    : ∀ {σ x₁ x₂}
             -> (σₜ : Γ ▻ intᵛ ⊢ σ            ∈ typeᵛ)
             ->       Γ        ⊢ x₁           ∈ ⟦ σₜ ⟧[ lᵛ ]
             ->       Γ        ⊢ x₂           ∈ ⟦ σₜ ⟧[ rᵛ ]
             ->       Γ        ⊢ path σ x₁ x₂ ∈ typeᵛ
    lᵗ       : Γ ⊢ l ∈ intᵛ
    rᵗ       : Γ ⊢ r ∈ intᵛ
    varᵗ     : ∀ v -> Γ ⊢ var v ∈ lookupᶜ v Γ
    ƛᵗ       : ∀ {σ b} {τₖ : Kripke n}
             -> Γ ▻ σ ⊢ b   ∈ instᵏ τₖ
             -> Γ     ⊢ ƛ b ∈ piᵛ σ τₖ
    δᵗ       : ∀ {x} {σₖ : Kripke n}
             -> (xₜ : Γ ▻ intᵛ ⊢ x   ∈ instᵏ σₖ)
             ->       Γ        ⊢ δ x ∈ pathᵛ σₖ ⟦ xₜ ⟧[ lᵛ ] ⟦ xₜ ⟧[ rᵛ ]
    _·ᵗ_     : ∀ {σ f x} {τₖ : Kripke n}
             ->       Γ ⊢ f     ∈ piᵛ σ τₖ
             -> (xₜ : Γ ⊢ x     ∈ σ)
             ->       Γ ⊢ f · x ∈ τₖ ⟦ xₜ ⟧ᵏ
    _#ᵗ_     : ∀ {p x₁ x₂ i} {σₖ : Kripke n}
                 {xₜ₁ : Γ ⊢ x₁ ∈ σₖ [ lᵛ ]ᵏ}
                 {xₜ₂ : Γ ⊢ x₂ ∈ σₖ [ rᵛ ]ᵏ}
             ->       Γ ⊢ p     ∈ pathᵛ σₖ (eval xₜ₁) (eval xₜ₂)
             -> (iₜ : Γ ⊢ i     ∈ intᵛ)
             ->       Γ ⊢ p # i ∈ σₖ ⟦ iₜ ⟧ᵏ
    coeᵗ     : ∀ {σ x j}
             -> (σₜ : Γ ▻ intᵛ ⊢ σ         ∈ typeᵛ)
             -> (jₜ : Γ        ⊢ j         ∈ intᵛ)
             ->       Γ        ⊢ x         ∈ ⟦ σₜ ⟧[ lᵛ ]
             ->       Γ        ⊢ coe σ j x ∈ ⟦ σₜ ⟧⟦ jₜ ⟧
    qcoerceᵗ : ∀ {σ τ x} -> quoteᵛ σ ≡ quoteᵛ τ -> Γ ⊢ x ∈ σ -> Γ ⊢ x ∈ τ

  ⟦_/_⟧ : ∀ {n m σ t} {Γ : Con n} -> m ↤ n -> Γ ⊢ t ∈ σ -> Value m
  ⟦ ρ / intᵗ          ⟧ = intᵛ
  ⟦ ρ / typeᵗ         ⟧ = typeᵛ
  ⟦ ρ / πᵗ σ τ        ⟧ = piᵛ ⟦ ρ / σ ⟧ ⟦ ρ / τ ⟧ᵏ
  ⟦ ρ / pathᵗ σ x₁ x₂ ⟧ = pathᵛ ⟦ ρ / σ ⟧ᵏ ⟦ ρ / x₁ ⟧ ⟦ ρ / x₂ ⟧
  ⟦ ρ / lᵗ            ⟧ = lᵛ
  ⟦ ρ / rᵗ            ⟧ = rᵛ
  ⟦ ρ / varᵗ v        ⟧ = lookupᵉ v ρ
  ⟦ ρ / ƛᵗ b          ⟧ = lamᵛ ⟦ ρ / b ⟧ᵏ
  ⟦ ρ / δᵗ x          ⟧ = dimᵛ ⟦ ρ / x ⟧ᵏ
  ⟦ ρ / f ·ᵗ x        ⟧ = ⟦ ρ / f ⟧ $ᵛ ⟦ ρ / x ⟧
  ⟦ ρ / p #ᵗ i        ⟧ = ⟦ ρ / p ⟧# ⟦ ρ / i ⟧
  ⟦ ρ / coeᵗ σ j x    ⟧ = coeᵛ ⟦ ρ / σ ⟧ᵏ ⟦ ρ / j ⟧ ⟦ ρ / x ⟧
  ⟦ ρ / qcoerceᵗ q t  ⟧ = ⟦ ρ / t ⟧

  ⟦_/_⟧ᵏ : ∀ {n m σ τ b} {Γ : Con n} -> m ↤ n -> Γ ▻ σ ⊢ b ∈ τ -> Kripke m
  ⟦ ρ / b ⟧ᵏ ι x = ⟦ renᵉ ι ρ ▷ x / b ⟧

  eval : ∀ {n σ t} {Γ : Con n} -> Γ ⊢ t ∈ σ -> Value n
  eval = ⟦ stopᵉ /_⟧
  
  ⟦_/_⟧#_ : ∀ {n m Γ x₁ x₂ t} {σₖ : Kripke n}
              {xₜ₁ : Γ ⊢ x₁ ∈ σₖ [ lᵛ ]ᵏ}
              {xₜ₂ : Γ ⊢ x₂ ∈ σₖ [ rᵛ ]ᵏ}
          -> m ↤ n -> Γ ⊢ t ∈ pathᵛ σₖ (eval xₜ₁) (eval xₜ₂) -> Value m -> Value m
  ⟦_/_⟧#_ {xₜ₁ = xₜ₁} ρ p lᵛ = ⟦ ρ / xₜ₁ ⟧
  ⟦_/_⟧#_ {xₜ₂ = xₜ₂} ρ p rᵛ = ⟦ ρ / xₜ₂ ⟧
  ⟦ ρ / p ⟧# iᵥ = case ⟦ ρ / p ⟧ of λ
    { (dimᵛ xₖ) -> xₖ [ iᵥ ]ᵏ
    ;  pᵥ       -> pᵥ #ᵛ iᵥ
    }

  _⟦_⟧ᵏ : ∀ {n t σ} {Γ : Con n} -> Kripke n -> Γ ⊢ t ∈ σ -> Value n
  k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

  ⟦_⟧[_] : ∀ {n b σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ b ∈ τ -> Value n -> Value n
  ⟦ b ⟧[ x ] = ⟦ stopᵉ ▷ x / b ⟧

  ⟦_⟧⟦_⟧ : ∀ {n b x σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ b ∈ τ -> Γ ⊢ x ∈ σ -> Value n
  ⟦ b ⟧⟦ x ⟧ = ⟦ b ⟧[ eval x ]

pattern _#⟨_,_⟩ᵗ_ p x₁ x₂ i = _#ᵗ_ {xₜ₁ = x₁} {xₜ₂ = x₂} p i

coerceᵗ : ∀ {n σ τ t} {Γ : Con n} -> Γ ⊢ t ∈ σ -> Maybe (Γ ⊢ t ∈ τ)
coerceᵗ {σ = σ} {τ} t⁺ = flip qcoerceᵗ t⁺ <$> quoteᵛ σ ≟ quoteᵛ τ

mutual
  infer : ∀ {n} {Γ : Con n} t -> Maybe (∃ (Γ ⊢ t ∈_))
  infer  int           = just (, intᵗ)
  infer  type          = just (, typeᵗ)
  infer (π σ τ)        = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , πᵗ σₜ τₜ) <$> check τ typeᵛ
  infer (path σ x₁ x₂) = check σ typeᵛ >>= λ σₜ ->
    (λ xₜ₁ xₜ₂ -> , pathᵗ σₜ xₜ₁ xₜ₂) <$> check x₁ ⟦ σₜ ⟧[ lᵛ ] ⊛ check x₂ ⟦ σₜ ⟧[ rᵛ ]
  infer  l             = just (, lᵗ)
  infer  r             = just (, rᵗ)
  infer (var v)        = just (, varᵗ v)
  infer (ƛ b)          = nothing
  infer (δ x)          = nothing
  infer (f · x)        = infer f >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _              -> nothing
    }
  infer (p # i)        = infer p >>= λ
    { (pathᵛ σₖ xᵥ₁ xᵥ₂ , pₜ) ->
         check i intᵛ                    >>= λ iₜ  ->
         check (quoteᵛ xᵥ₁) (σₖ [ lᵛ ]ᵏ) >>= λ xₜ₁ ->
         check (quoteᵛ xᵥ₂) (σₖ [ rᵛ ]ᵏ) >>= λ xₜ₂ ->
               (λ pₜ′ -> σₖ ⟦ iₜ ⟧ᵏ , pₜ′ #⟨ xₜ₁ , xₜ₂ ⟩ᵗ iₜ)
           <$>  coerceᵗ {τ = pathᵛ σₖ (eval xₜ₁) (eval xₜ₂)} pₜ
    ;  _                      -> nothing
    }
  infer (coe σ j x)    = check σ typeᵛ >>= λ σₜ -> check j intᵛ >>= λ jₜ ->
    (λ xₜ -> , coeᵗ σₜ jₜ xₜ) <$> check x ⟦ σₜ ⟧[ lᵛ ]

  check : ∀ {n} {Γ : Con n} t σ -> Maybe (Γ ⊢ t ∈ σ)
  check (ƛ b) (piᵛ σ τₖ)         = ƛᵗ <$> check b (instᵏ τₖ)
  check (δ x) (pathᵛ σₖ xᵥ₁ xᵥ₂) = check x (instᵏ σₖ) >>= λ xₜ -> coerceᵗ (δᵗ {σₖ = σₖ} xₜ)
  check  t     σ                 = infer t >>= coerceᵗ ∘ proj₂

check₀ : ∀ t σ -> Maybe (ε ⊢ t ∈ σ)
check₀ = check

typecheck : ∀ t σ -> _
typecheck t σ = check₀ σ typeᵛ >>=⊤ λ σₜ -> check₀ t (eval σₜ) >>=⊤ id

_∈_ : Term⁽⁾ -> Type⁽⁾ -> Set
t ∈ σ = recᵗ (T ∘ is-just) ⊥ $ check₀ σ typeᵛ >>=ᵗ λ σₜ -> check₀ t (eval σₜ)
