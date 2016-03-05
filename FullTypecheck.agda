{-# OPTIONS --rewriting --no-termination-check #-}

module Cubes.FullTypecheck where

open import Cubes.Typed

{-# BUILTIN REWRITE _≡_ #-}

postulate
  eval-quoteᵛ : ∀ {n} {x : Value n} -> ⟦ stopᵉ / quoteᵛ x ⟧ᵛ ≡ x
  instᵏ-abstᵏ : ∀ {n} {x : Value (suc n)}
              -> ⟦ (stopᵉ ▷ varᵛ fzero) / quoteᵛ (ren (keep top) x) ⟧ᵛ ≡ x

{-# REWRITE eval-quoteᵛ #-}
-- We need this only because of the `δᵗ' constructor.
-- But it would also be required if we allow lambdas to carry types in raw terms.
{-# REWRITE instᵏ-abstᵏ #-}

private
  test-eval-quoteᵛ : ∀ {n} {x : Value n} -> eval (quoteᵛ x) ≡ x
  test-eval-quoteᵛ = refl

  test-instᵏ-abstᵏ : ∀ {n} {x : Value (suc n)} -> instᵏ (abstᵏ x) ≡ x
  test-instᵏ-abstᵏ = refl

infix  4 _⊢_∈ᵗ_
infix  4 ⊢*_
infixl 8 _[_]ᵗ

_⊢_∈ᵗ_ : ∀ {n} -> (Γ : Con n) -> Term n -> Value n -> Set
Γ ⊢ t ∈ᵗ σ = Γ ⊢ t ∈ σ × Γ ⊢ quoteᵛ σ ∈ typeᵛ

postulate
  shiftᵗ : ∀ {n σ τ} {Γ : Con n} x -> Γ ⊢ quoteᵛ x ∈ σ -> Γ ▻ τ ⊢ quoteᵛ (shift x) ∈ shift σ
  _[_]ᵗ  : ∀ {n σ τ x y} {Γ : Con n} -> Γ ▻ σ ⊢ y ∈ τ -> Γ ⊢ x ∈ σ -> Γ ⊢ y [ x ] ∈ τ ⟦ x ⟧ᵛ
  normᵗ  : ∀ {n x σ} {Γ : Con n} -> Γ ⊢ x ∈ σ -> Γ ⊢ norm x ∈ σ

data ⊢*_ : ∀ {n} -> Con n -> Set where
  ø   : ⊢* ε
  _▷_ : ∀ {n σ} {Γ : Con n} -> ⊢* Γ -> Γ ⊢ quoteᵛ σ ∈ typeᵛ -> ⊢* Γ ▻ σ

lookupᵗ : ∀ {n} {Γ : Con n} -> (v : Fin n) -> ⊢* Γ -> Γ ⊢ quoteᵛ (lookupᶜ v Γ) ∈ typeᵛ
lookupᵗ {Γ = Γ ▻ σ}  fzero   (ρ ▷ t) = shiftᵗ σ t
lookupᵗ {Γ = Γ ▻ σ} (fsuc i) (ρ ▷ t) = shiftᵗ (lookupᶜ i Γ) (lookupᵗ i ρ)

-- Holds definitionally:
-- quoteᵛ (instᵏ k) [ x ]
-- quoteᵛ ⟦ quoteᵛ (instᵏ k) ⟧⟦ x ⟧
-- quoteᵛ ⟦ quoteᵛ (instᵏ k) ⟧[ eval x ]
-- quoteᵛ (instᵏ k [ eval x ]ᵛ)
-- quoteᵛ (instᵏ k ⟦ x ⟧ᵛ)
-- quoteᵛ (k ⟦ x ⟧ᵏ)
-- _/ᵏ_[_]ᵗ : ∀ {n σ τ x} {Γ : Con n}
--          -> (k : Kripke n)
--          -> Γ ▻ σ ⊢ quoteᵛ (instᵏ k) ∈ τ
--          -> Γ ⊢ x ∈ σ
--          -> Γ ⊢ quoteᵛ (k ⟦ x ⟧ᵏ) ∈ τ ⟦ x ⟧ᵛ
-- k /ᵏ b [ x ]ᵗ = b [ x ]ᵗ

mutual
  infer : ∀ {n} {Γ : Con n} -> ⊢* Γ -> ∀ t -> Maybe (∃ (Γ ⊢ t ∈ᵗ_))
  infer ρ (int             ) = just (, intᵗ  , typeᵗ)
  infer ρ (type            ) = just (, typeᵗ , typeᵗ)
  infer ρ (π σ τ           ) =
    check ρ  σ       typeᵗ >>= λ σₜ  ->
    -- Alternatively instead of using `normᵗ'
    -- check ρ (norm σ) typeᵗ >>= λ σₙₜ ->
      (λ τₜ -> , πᵗ σₜ τₜ , typeᵗ) <$> check (ρ ▷ normᵗ σₜ) τ typeᵗ
  infer ρ (path σ x₁ x₂    ) =
    check (ρ ▷ intᵗ) σ typeᵗ >>= λ σₜ ->
          (λ xₜ₁ xₜ₂ -> , pathᵗ σₜ xₜ₁ xₜ₂ , typeᵗ)
      <$>  check ρ x₁ (σₜ [ lᵗ ]ᵗ)
       ⊛   check ρ x₂ (σₜ [ rᵗ ]ᵗ)
  infer ρ (l               ) = just (, lᵗ , intᵗ)
  infer ρ (r               ) = just (, rᵗ , intᵗ)
  infer ρ (var v           ) = just (, varᵗ v , lookupᵗ v ρ)
  infer ρ (ƛ b             ) = nothing
  infer ρ (δ x             ) =
    (λ{ (σ , xₜ , σₜ) -> , δᵗ xₜ , pathᵗ σₜ (xₜ [ lᵗ ]ᵗ) (xₜ [ rᵗ ]ᵗ) }) <$> infer (ρ ▷ intᵗ) x  
  infer ρ (f · x           ) = infer ρ f >>= λ
    { (piᵛ σ τₖ , fₜ , πᵗ σₜ τₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ , τₜ [ xₜ ]ᵗ) <$> check ρ x σₜ
    ;  _                         -> nothing
    }
  infer ρ (p #⟨ x₁ , x₂ ⟩ i) = infer ρ p >>= λ
    { (pathᵛ σₖ xᵥ₁ xᵥ₂ , pₜ , pathᵗ σₜ xₜ₁ xₜ₂) ->
          (λ pₜ′ xₜ₁′ xₜ₂′ iₜ -> σₖ ⟦ i ⟧ᵏ , pₜ′ #⟨ xₜ₁′ , xₜ₂′ ⟩ᵗ iₜ , σₜ [ iₜ ]ᵗ)
        <$> coerceᵗ {τ = pathᵛ σₖ (eval x₁) (eval x₂)} pₜ
         ⊛  check ρ x₁ (σₜ [ lᵗ ]ᵗ)
         ⊛  check ρ x₂ (σₜ [ rᵗ ]ᵗ)
         ⊛  check ρ i   intᵗ
    ;  _                                         -> nothing
    }
  infer ρ (coe σ x j       ) =
    check (ρ ▷ intᵗ) σ typeᵗ >>= λ σₜ ->
      (λ xₜ jₜ -> , coeᵗ σₜ xₜ jₜ , σₜ [ jₜ ]ᵗ) <$> check ρ x (σₜ [ lᵗ ]ᵗ) ⊛ check ρ j intᵗ

  check : ∀ {n σ} {Γ : Con n} -> ⊢* Γ -> (t : Term n) -> Γ ⊢ quoteᵛ σ ∈ typeᵛ -> Maybe (Γ ⊢ t ∈ σ)
  check {σ = σ       } {Γ} ρ  t    σₜ with generalize (Γ ⊢ quoteᵛ σ ∈_) σₜ
  check {σ = piᵛ σ τₖ}     ρ (ƛ b) _  | , πᵗ σₜ τₜ , refl = ƛᵗ σₜ <$> check (ρ ▷ σₜ) b τₜ
  check                    ρ  t    σₜ | _                 = infer ρ t >>= coerceᵗ ∘ proj₁ ∘ proj₂

typecheck : ∀ t σ -> Maybe (ε ⊢ t ∈ᵗ σ)
typecheck t σ = check ø (quoteᵛ σ) typeᵗ >>= λ σₜ -> (_, σₜ) <$> check ø t σₜ
