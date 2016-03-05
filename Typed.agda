module Cubes.Typed where

open import Cubes.Core public
open import Cubes.NbE  public

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Con {Value} n) : Term n -> Value n -> Set where
  intᵗ      : Γ ⊢ int  ∈ typeᵛ
  typeᵗ     : Γ ⊢ type ∈ typeᵛ
  πᵗ        : ∀ {σ τ}
            -> Γ          ⊢ σ     ∈ typeᵛ
            -> Γ ▻ eval σ ⊢ τ     ∈ typeᵛ
            -> Γ          ⊢ π σ τ ∈ typeᵛ
  pathᵗ     : ∀ {σ x₁ x₂}
            -> Γ ▻ intᵛ ⊢ σ            ∈ typeᵛ
            -> Γ        ⊢ x₁           ∈ ⟦ σ ⟧⟦ l ⟧
            -> Γ        ⊢ x₂           ∈ ⟦ σ ⟧⟦ r ⟧
            -> Γ        ⊢ path σ x₁ x₂ ∈ typeᵛ
  lᵗ        : Γ ⊢ l ∈ intᵛ
  rᵗ        : Γ ⊢ r ∈ intᵛ
  varᵗ      : ∀ v -> Γ ⊢ var v ∈ lookupᶜ v Γ
  ƛᵗ        : ∀ {σ b} {τₖ : Kripke n}
            -> Γ     ⊢ quoteᵛ σ ∈ typeᵛ
            -> Γ ▻ σ ⊢ b        ∈ instᵏ τₖ
            -> Γ     ⊢ ƛ b      ∈ piᵛ σ τₖ
  δᵗ        : ∀ {σ x}
            -> Γ ▻ intᵛ ⊢ x   ∈ σ
            -> Γ        ⊢ δ x ∈ pathᵛ (abstᵏ σ) ⟦ x ⟧⟦ l ⟧ ⟦ x ⟧⟦ r ⟧
  _·ᵗ_      : ∀ {σ f x} {τₖ : Kripke n}
            -> Γ ⊢ f     ∈ piᵛ σ τₖ
            -> Γ ⊢ x     ∈ σ
            -> Γ ⊢ f · x ∈ τₖ ⟦ x ⟧ᵏ
  _#⟨_,_⟩ᵗ_ : ∀ {p x₁ x₂ i} {σₖ : Kripke n}
            -> Γ ⊢ p                ∈ pathᵛ σₖ (eval x₁) (eval x₂)
            -> Γ ⊢ x₁               ∈ σₖ ⟦ l ⟧ᵏ
            -> Γ ⊢ x₂               ∈ σₖ ⟦ r ⟧ᵏ
            -> Γ ⊢ i                ∈ intᵛ
            -> Γ ⊢ p #⟨ x₁ , x₂ ⟩ i ∈ σₖ ⟦ i ⟧ᵏ
  coeᵗ      : ∀ {σ x j}
            -> Γ ▻ intᵛ ⊢ σ         ∈ typeᵛ
            -> Γ        ⊢ x         ∈ ⟦ σ ⟧⟦ l ⟧
            -> Γ        ⊢ j         ∈ intᵛ
            -> Γ        ⊢ coe σ x j ∈ ⟦ σ ⟧⟦ j ⟧
  qcoerceᵗ  : ∀ {σ τ x} -> quoteᵛ σ ≡ quoteᵛ τ -> Γ ⊢ x ∈ σ -> Γ ⊢ x ∈ τ

coerceᵗ : ∀ {n σ τ t} {Γ : Con n} -> Γ ⊢ t ∈ σ -> Maybe (Γ ⊢ t ∈ τ)
coerceᵗ {σ = σ} {τ} t⁺ = flip qcoerceᵗ t⁺ <$> quoteᵛ σ ≟ quoteᵛ τ
