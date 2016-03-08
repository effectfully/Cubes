{-# OPTIONS --no-termination-check #-}

module Cubes.Typecheck where

open import Cubes.Core public

infix  4 _⊢_
infixl 8 _⟦_⟧ᵏ
infixl 2 _∋_

mutual
  data _⊢_ {n} (Γ : Con n) : Value n -> Set where
    intᵗ     : Γ ⊢ typeᵛ
    typeᵗ    : Γ ⊢ typeᵛ
    πᵗ       :  (σₜ : Γ           ⊢ typeᵛ)
             ->       Γ ▻ eval σₜ ⊢ typeᵛ
             ->       Γ           ⊢ typeᵛ
    pathᵗ    :  (σₜ : Γ ▻ intᵛ ⊢ typeᵛ)
             ->       Γ        ⊢ ⟦ σₜ ⟧[ lᵛ ]
             ->       Γ        ⊢ ⟦ σₜ ⟧[ rᵛ ]
             ->       Γ        ⊢ typeᵛ
    lᵗ       : Γ ⊢ intᵛ
    rᵗ       : Γ ⊢ intᵛ
    varᵗ     : ∀ v -> Γ ⊢ lookupᶜ v Γ
    ƛᵗ       : ∀ {σ} {τₖ : Kripke n}
             -> Γ ▻ σ ⊢ instᵏ τₖ
             -> Γ     ⊢ piᵛ σ τₖ
    δᵗ       : {σₖ : Kripke n}
             -> (xₜ : Γ ▻ intᵛ ⊢ instᵏ σₖ)
             ->       Γ        ⊢ pathᵛ σₖ ⟦ xₜ ⟧[ lᵛ ] ⟦ xₜ ⟧[ rᵛ ]
    _·ᵗ_     : ∀ {σ} {τₖ : Kripke n}
             ->       Γ ⊢ piᵛ σ τₖ
             -> (xₜ : Γ ⊢ σ)
             ->       Γ ⊢ τₖ ⟦ xₜ ⟧ᵏ
    _#ᵗ_     : {σₖ : Kripke n} {xₜ₁ : Γ ⊢ σₖ [ lᵛ ]ᵏ} {xₜ₂ : Γ ⊢ σₖ [ rᵛ ]ᵏ}
             ->       Γ ⊢ pathᵛ σₖ (eval xₜ₁) (eval xₜ₂)
             -> (iₜ : Γ ⊢ intᵛ)
             ->       Γ ⊢ σₖ ⟦ iₜ ⟧ᵏ
    coeᵗ     :  (σₜ : Γ ▻ intᵛ ⊢ typeᵛ)
             -> (jₜ : Γ        ⊢ intᵛ)
             ->       Γ        ⊢ ⟦ σₜ ⟧[ lᵛ ]
             ->       Γ        ⊢ ⟦ σₜ ⟧⟦ jₜ ⟧
    qcoerceᵗ : ∀ {σ τ} -> quoteᵛ₀ σ ≡ quoteᵛ₀ τ -> Γ ⊢ σ -> Γ ⊢ τ
    wkᵗ      : ∀ {σ} -> ε ⊢ σ -> Γ ⊢ wk₀ σ

  ⟦_/_⟧ : ∀ {n m σ} {Γ : Con n} -> m ↤ n -> Γ ⊢ σ -> Value m
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
  ⟦ ρ / wkᵗ t         ⟧ = wk₀ (eval t)

  ⟦_/_⟧ᵏ : ∀ {n m σ τ} {Γ : Con n} -> m ↤ n -> Γ ▻ σ ⊢ τ -> Kripke m
  ⟦ ρ / b ⟧ᵏ ι x = ⟦ renᵉ ι ρ ▷ x / b ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value n
  eval = ⟦ stopᵉ /_⟧

  ⟦_/_⟧#_ : ∀ {n m Γ} {σₖ : Kripke n}
              {xₜ₁ : Γ ⊢ σₖ [ lᵛ ]ᵏ}
              {xₜ₂ : Γ ⊢ σₖ [ rᵛ ]ᵏ}
          -> m ↤ n -> Γ ⊢ pathᵛ σₖ (eval xₜ₁) (eval xₜ₂) -> Value m -> Value m
  ⟦_/_⟧#_ {xₜ₁ = xₜ₁} ρ p lᵛ = ⟦ ρ / xₜ₁ ⟧
  ⟦_/_⟧#_ {xₜ₂ = xₜ₂} ρ p rᵛ = ⟦ ρ / xₜ₂ ⟧
  ⟦ ρ / p ⟧# iᵥ = case ⟦ ρ / p ⟧ of λ
    { (dimᵛ xₖ) -> xₖ [ iᵥ ]ᵏ
    ;  pᵥ       -> pᵥ #ᵛ iᵥ
    }

  _⟦_⟧ᵏ : ∀ {n σ} {Γ : Con n} -> Kripke n -> Γ ⊢ σ -> Value n
  k ⟦ x ⟧ᵏ   = k [ eval x ]ᵏ

  ⟦_⟧[_] : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Value n -> Value n
  ⟦ b ⟧[ x ] = ⟦ stopᵉ ▷ x / b ⟧

  ⟦_⟧⟦_⟧ : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Value n
  ⟦ b ⟧⟦ x ⟧ = ⟦ b ⟧[ eval x ]

pattern _#⟨_,_⟩ᵗ_ p x₁ x₂ i = _#ᵗ_ {xₜ₁ = x₁} {xₜ₂ = x₂} p i

coerceᵗ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> Maybe (Γ ⊢ τ)
coerceᵗ {σ = σ} {τ} t = flip qcoerceᵗ t <$> quoteᵛ₀ σ ≟ quoteᵛ₀ τ

Typed : Set
Typed = ∃ λ (σ⁺ : Value⁺) -> ∀ {n} {Γ : Con n} -> Γ ⊢ σ⁺

open TermWith Typed public

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> Maybe (∃ (Γ ⊢_))
  infer (pure (, tₜ⁺)) = just (, tₜ⁺)
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
  infer (coe σ j x)    =
    check σ typeᵛ >>= λ σₜ -> (λ jₜ xₜ -> , coeᵗ σₜ jₜ xₜ) <$> check j intᵛ ⊛ check x ⟦ σₜ ⟧[ lᵛ ]

  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value n) -> Maybe (Γ ⊢ σ)
  check (ƛ b) (piᵛ σ τₖ)         = ƛᵗ <$> check b (instᵏ τₖ)
  check (δ x) (pathᵛ σₖ xᵥ₁ xᵥ₂) = check x (instᵏ σₖ) >>= λ xₜ -> coerceᵗ (δᵗ {σₖ = σₖ} xₜ)
  check  t     σ                 = infer t >>= coerceᵗ ∘ proj₂

typecheck : Term⁽⁾ -> Value⁽⁾ -> Maybe Term⁺
typecheck t σ = (λ tₜ {_} -> pure $ wk₀ σ , wkᵗ tₜ) <$> check t σ 

_∋_ : ∀ σ t -> _
σ ∋ t = check {Γ = ε} σ typeᵛ >>=⊤ λ σₜ -> typecheck t (eval σₜ) >>=⊤ id
