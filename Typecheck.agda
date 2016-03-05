{-# OPTIONS --rewriting --no-termination-check #-}

module Cubes.Typecheck where

open import Cubes.Core
open import Cubes.NbE

{-# BUILTIN REWRITE _≡_ #-}

postulate
  eval-quoteᵛ : ∀ {n} {x : Value n} -> ⟦ stopᵉ / quoteᵛ x ⟧ᵛ ≡ x
  instᵏ-abstᵏ : ∀ {n} {x : Value (suc n)}
              -> ⟦ (stopᵉ ▷ varᵛ fzero) / quoteᵛ (ren (keep top) x) ⟧ᵛ ≡ x

{-# REWRITE eval-quoteᵛ #-}
{-# REWRITE instᵏ-abstᵏ #-}

private
  test-eval-quoteᵛ : ∀ {n} {x : Value n} -> eval (quoteᵛ x) ≡ x
  test-eval-quoteᵛ = refl

  test-instᵏ-abstᵏ : ∀ {n} {x : Value (suc n)} -> instᵏ (abstᵏ x) ≡ x
  test-instᵏ-abstᵏ = refl

infix  4 _⊢_∈_ _⊢_∈ᵗ_
infix  4 ⊢*_
infixl 8 _[_]ᵗ

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
--   δᵗ        : ∀ {x} {σₖ : Kripke n}
--             -> Γ ▻ intᵛ ⊢ x   ∈ instᵏ σₖ
--             -> Γ        ⊢ δ x ∈ pathᵛ σₖ ⟦ x ⟧⟦ l ⟧ ⟦ x ⟧⟦ r ⟧
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
  quote-coe : ∀ {σ τ x} -> quoteᵛ σ ≡ quoteᵛ τ -> Γ ⊢ x ∈ σ -> Γ ⊢ x ∈ τ

data ⊢*_ : ∀ {n} -> Con n -> Set where
  ø   : ⊢* ε
  _▷_ : ∀ {n σ} {Γ : Con n} -> ⊢* Γ -> Γ ⊢ quoteᵛ σ ∈ typeᵛ -> ⊢* Γ ▻ σ

coerce : ∀ {n σ τ t} {Γ : Con n} -> Γ ⊢ t ∈ σ -> Maybe (Γ ⊢ t ∈ τ)
coerce {σ = σ} {τ} t⁺ = flip quote-coe t⁺ <$> quoteᵛ σ ≟ quoteᵛ τ

-- ren*

shift* : ∀ {n} {σ τ} {Γ : Con n} x -> Γ ⊢ quoteᵛ x ∈ σ -> Γ ▻ τ ⊢ quoteᵛ (shift x) ∈ shift σ
shift* = {!!}

lookup* : ∀ {n} {Γ : Con n} -> (v : Fin n) -> ⊢* Γ -> Γ ⊢ quoteᵛ (lookupᶜ v Γ) ∈ typeᵛ
lookup* {Γ = Γ ▻ σ}  fzero   (ρ ▷ t) = shift* σ t
lookup* {Γ = Γ ▻ σ} (fsuc i) (ρ ▷ t) = shift* (lookupᶜ i Γ) (lookup* i ρ)

_[_]ᵗ : ∀ {n σ τ x y} {Γ : Con n} -> Γ ▻ σ ⊢ y ∈ τ -> Γ ⊢ x ∈ σ -> Γ ⊢ y [ x ] ∈ τ ⟦ x ⟧ᵛ
_[_]ᵗ = {!!}

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

generalize : ∀ {α β} {A : Set α} {x} -> (B : A -> Set β) -> B x -> ∃ λ x' -> B x' × x ≡ x'
generalize B y = , y , refl

-- Subject reduction.
-- normᵗ : ∀ {n x σ} {Γ : Con n} -> Γ ⊢ x ∈ σ -> Γ ⊢ norm x ∈ σ
-- normᵗ = {!!}

_⊢_∈ᵗ_ : ∀ {n} -> (Γ : Con n) -> Term n -> Value n -> Set
Γ ⊢ t ∈ᵗ σ = Γ ⊢ t ∈ σ × Γ ⊢ quoteᵛ σ ∈ typeᵛ

mutual
  infer : ∀ {n} {Γ : Con n} -> ⊢* Γ -> ∀ t -> Maybe (∃ (Γ ⊢ t ∈ᵗ_))
  infer ρ (int             ) = just (, intᵗ  , typeᵗ)
  infer ρ (type            ) = just (, typeᵗ , typeᵗ)
  infer ρ (π σ τ           ) =
--    check ρ σ typeᵗ >>= λ σₜ ->
--      (λ τₜ -> , πᵗ σₜ τₜ , typeᵗ) <$> check (ρ ▷ normᵗ σₜ) τ typeᵗ
    check ρ  σ       typeᵗ >>= λ σₜ  ->
    check ρ (norm σ) typeᵗ >>= λ σₙₜ ->
      (λ τₜ -> , πᵗ σₜ τₜ , typeᵗ) <$> check (ρ ▷ σₙₜ) τ typeᵗ
  infer ρ (path σ x₁ x₂    ) =
    check (ρ ▷ intᵗ) σ typeᵗ >>= λ σₜ ->
          (λ xₜ₁ xₜ₂ -> , pathᵗ σₜ xₜ₁ xₜ₂ , typeᵗ)
      <$>  check ρ x₁ (σₜ [ lᵗ ]ᵗ)
       ⊛   check ρ x₂ (σₜ [ rᵗ ]ᵗ)
  infer ρ (l               ) = just (, lᵗ , intᵗ)
  infer ρ (r               ) = just (, rᵗ , intᵗ)
  infer ρ (var v           ) = just (, varᵗ v , lookup* v ρ)
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
        <$> coerce {τ = pathᵛ σₖ (eval x₁) (eval x₂)} pₜ
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
  check                    ρ  t    σₜ | _                 = infer ρ t >>= coerce ∘ proj₁ ∘ proj₂

typecheck : ∀ t σ -> Maybe (ε ⊢ t ∈ᵗ σ)
typecheck t σ = check ø (quoteᵛ σ) typeᵗ >>= λ σₜ -> (_, σₜ) <$> check ø t σₜ
