{-# OPTIONS --no-termination-check #-}

module Cubes.Typecheck where

open import Cubes.Typed

mutual
  infer : ∀ {n t} {Γ : Con n} -> Maybe (∃ (Γ ⊢ t ∈_))
  infer {t = int             } = just (, intᵗ)
  infer {t = type            } = just (, typeᵗ)
  infer {t = π σ τ           } = (λ σₜ τₜ -> , πᵗ σₜ τₜ) <$> check ⊛ check
  infer {t = path σ x₁ x₂    } = (λ σₜ xₜ₁ xₜ₂ -> , pathᵗ σₜ xₜ₁ xₜ₂) <$> check ⊛ check ⊛ check
  infer {t = l               } = just (, lᵗ)
  infer {t = r               } = just (, rᵗ)
  infer {t = var v           } = just (, varᵗ v)
  infer {t = ƛ b             } = nothing
  infer {t = δ x             } = (uncurry λ σ xₜ -> , δᵗ xₜ) <$> infer
  infer {t = f · x           } = infer >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check
    ;  _              -> nothing
    }
  infer {t = p #⟨ x₁ , x₂ ⟩ i} = infer >>= λ
    { (pathᵛ σₖ xᵥ₁ xᵥ₂ , pₜ) ->
        (λ pₜ′ xₜ₁′ xₜ₂′ iₜ -> σₖ ⟦ i ⟧ᵏ , pₜ′ #⟨ xₜ₁′ , xₜ₂′ ⟩ᵗ iₜ)
           <$> coerceᵗ {τ = pathᵛ σₖ (eval x₁) (eval x₂)} pₜ ⊛ check ⊛ check ⊛ check
    ;  _                      -> nothing
    }
  infer {t = coe σ x j       } = (λ σₜ xₜ jₜ -> , coeᵗ σₜ xₜ jₜ) <$> check ⊛ check ⊛ check

  check : ∀ {n t σ} {Γ : Con n} -> Maybe (Γ ⊢ t ∈ σ)
  check {t = ƛ b} {piᵛ σ τₖ} = ƛᵗ <$> check ⊛ check
  check {t = _  } {_       } = infer >>= coerceᵗ ∘ proj₂

typecheck : ∀ t σ -> Maybe (ε ⊢ t ∈ σ)
typecheck t σ = check {t = quoteᵛ σ} {typeᵛ} {ε} >> check
