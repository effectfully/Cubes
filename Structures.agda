module Cubes.Structures where

open import Cubes.Prelude public

infix 4 _⊑_

data _⊑_ : ℕ -> ℕ -> Set where
  stop : ∀ {n}   -> n ⊑ n
  skip : ∀ {n m} -> n ⊑ m -> n     ⊑ suc m
  keep : ∀ {n m} -> n ⊑ m -> suc n ⊑ suc m

top : ∀ {n} -> n ⊑ suc n
top = skip stop

full : ∀ {n} -> 0 ⊑ n
full {0}     = stop
full {suc n} = skip full

keep+ : ∀ {n m} -> n ⊑ n + m
keep+ {0}     = full
keep+ {suc n} = keep keep+

_∘ˢ_ : ∀ {n m p} -> m ⊑ p -> n ⊑ m -> n ⊑ p
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ stop   = keep  κ
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

Weakens : (ℕ -> Set) -> Set
Weakens Fam = ∀ {n m} -> Fam n -> Fam (n + m)

Renames : (ℕ -> Set) -> Set
Renames Fam = ∀ {n m} -> n ⊑ m -> Fam n -> Fam m

Unrenames : (ℕ -> Set) -> Set
Unrenames Fam = ∀ {n m} -> n ⊑ m -> Fam m -> Maybe (Fam n)

module Kripke (Fam : ℕ -> Set) where
  infixl 8 _[_]ᵏ
  infixr 9 _∘ᵏ_

  Kripke : ℕ -> Set
  Kripke n = ∀ {m} -> n ⊑ m -> Fam m -> Fam m

  _[_]ᵏ : ∀ {n} -> Kripke n -> Fam n -> Fam n
  k [ t ]ᵏ = k stop t

  renᵏ : Renames Kripke
  renᵏ ι k κ = k (κ ∘ˢ ι)

  wkᵏ : Weakens Kripke
  wkᵏ = renᵏ keep+

  _∘ᵏ_ : ∀ {n} -> Kripke n -> Kripke n -> Kripke n
  (k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

record Context (Fam : ℕ -> Set) : Set where
  field ren : Renames Fam

  infixl 5 _▻_
  infix  4 _⊑ᶜ_

  shift : ∀ {n} -> Fam n -> Fam (suc n)
  shift = ren top

  data Con : ℕ -> Set where
    ε   : Con 0
    _▻_ : ∀ {n} -> Con n -> Fam n -> Con (suc n)

  lookupᶜ : ∀ {n} -> Fin n -> Con n -> Fam n
  lookupᶜ  fzero   (Γ ▻ t) = shift t
  lookupᶜ (fsuc v) (Γ ▻ t) = shift (lookupᶜ v Γ)

  slookupᶜ : ∀ {n} -> (i : Fin n) -> Con n -> Fam (revert i)
  slookupᶜ  fzero   (Γ ▻ t) = t
  slookupᶜ (fsuc v) (Γ ▻ t) = slookupᶜ v Γ

  mutual
    data _⊑ᶜ_ : ∀ {n m} -> Con n -> Con m -> Set where
      stopᶜ : ∀ {n}     {Γ : Con n}             ->      Γ ⊑ᶜ Γ
      skipᶜ : ∀ {n m σ} {Γ : Con n} {Δ : Con m} ->      Γ ⊑ᶜ Δ  -> Γ     ⊑ᶜ Δ ▻ σ
      keepᶜ : ∀ {n m σ} {Γ : Con n} {Δ : Con m} -> (ι : Γ ⊑ᶜ Δ) -> Γ ▻ σ ⊑ᶜ Δ ▻ ren (eraseᶜ ι) σ

    eraseᶜ : ∀ {n m} {Γ : Con n} {Δ : Con m} -> Γ ⊑ᶜ Δ -> n ⊑ m
    eraseᶜ  stopᶜ    = stop
    eraseᶜ (skipᶜ ι) = skip (eraseᶜ ι)
    eraseᶜ (keepᶜ ι) = keep (eraseᶜ ι)
open Context {{...}} public

record Append (Fam : ℕ -> Set) {{context : Context Fam}} : Set where
  field wk : Weakens Fam

  infixl 5 _▻▻_

  wk₀ : ∀ {n} -> Fam 0 -> Fam n
  wk₀ = wk

  _▻▻_ : ∀ {n m} -> Con m -> Con n -> Con (n + m)
  Δ ▻▻  ε      = Δ
  Δ ▻▻ (Γ ▻ σ) = Δ ▻▻ Γ ▻ wk σ
open Append {{...}} public

record Backwards (Fam : ℕ -> Set) : Set where
  field unren : Unrenames Fam

  unshift : ∀ {n} -> Fam (suc n) -> Maybe (Fam n)
  unshift = unren top
open Backwards {{...}} public

record Environment Fam {{context : Context Fam}} : Set where
  field fresh : ∀ {n} -> Fam (suc n)

  open Kripke Fam

  infix  4 _↤_
  infixl 5 _▷_

  instᵏ : ∀ {n} -> Kripke n -> Fam (suc n)
  instᵏ k = k top fresh

  data _↤_ m : ℕ -> Set where
    ø   : m ↤ 0
    _▷_ : ∀ {n} -> m ↤ n -> Fam m -> m ↤ suc n

  lookupᵉ : ∀ {n m} -> Fin n -> m ↤ n -> Fam m
  lookupᵉ  fzero   (ρ ▷ t) = t
  lookupᵉ (fsuc i) (ρ ▷ t) = lookupᵉ i ρ

  renᵉ : ∀ {n} -> Renames (_↤ n)
  renᵉ ι  ø      = ø
  renᵉ ι (ρ ▷ t) = renᵉ ι ρ ▷ ren ι t

  skipᵉ : ∀ {n m} -> m ↤ n -> suc m ↤ n
  skipᵉ = renᵉ top

  keepᵉ : ∀ {n m} -> m ↤ n -> suc m ↤ suc n
  keepᵉ ρ = skipᵉ ρ ▷ fresh

  stopᵉ : ∀ {n} -> n ↤ n
  stopᵉ {0}     = ø
  stopᵉ {suc n} = keepᵉ stopᵉ
open Environment {{...}} public

-- Agda doesn't pick these instances for some reason.
-- module _ {Fam : ℕ -> Set} where
--   open Kripke Fam

--   instance
--     kripkeContext : Context Kripke
--     kripkeContext = record { ren = λ ι k κ -> k (κ ∘ˢ ι) }

--     kripkeAppend : Append Kripke
--     kripkeAppend = record { wk = ren keep+ }

instance
  finContext : Context Fin
  finContext = record { ren = go } where
    go : Renames Fin
    go  stop     i       = i
    go (skip ι)  i       = fsuc (go ι i)
    go (keep ι)  fzero   = fzero
    go (keep ι) (fsuc i) = fsuc (go ι i)

  finBackwards : Backwards Fin
  finBackwards = record { unren = go } where
    go : Unrenames Fin
    go  stop     i       = just i
    go (skip ι)  fzero   = nothing
    go (skip ι) (fsuc i) = go ι i
    go (keep ι)  fzero   = just fzero
    go (keep ι) (fsuc i) = fsuc <$> go ι i

  finEnvironment : Environment Fin
  finEnvironment = record { fresh = fzero }
