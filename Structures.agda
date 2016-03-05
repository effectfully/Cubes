{-# OPTIONS --rewriting #-}

module Cubes.Structures where

open import Cubes.Prelude public

data _⊑_ : ℕ -> ℕ -> Set where
  stop : ∀ {n}   -> n ⊑ n
  skip : ∀ {n m} -> n ⊑ m -> n     ⊑ suc m
  keep : ∀ {n m} -> n ⊑ m -> suc n ⊑ suc m

top : ∀ {n} -> n ⊑ suc n
top = skip stop

full : ∀ {n} -> 0 ⊑ n
full {0}     = stop
full {suc n} = skip full

_∘ˢ_ : ∀ {n m p} -> m ⊑ p -> n ⊑ m -> n ⊑ p
stop   ∘ˢ ι      = ι
skip κ ∘ˢ ι      = skip (κ ∘ˢ ι)
keep κ ∘ˢ stop   = keep  κ
keep κ ∘ˢ skip ι = skip (κ ∘ˢ ι)
keep κ ∘ˢ keep ι = keep (κ ∘ˢ ι)

Renames : (ℕ -> Set) -> Set
Renames Fam = ∀ {n m} -> n ⊑ m -> Fam n -> Fam m

module Kripke (Fam : ℕ -> Set) where
  infixl 8 _[_]ᵏ
  infixr 9 _∘ᵏ_

  Kripke : ℕ -> Set
  Kripke n = ∀ {m} -> n ⊑ m -> Fam m -> Fam m

  renᵏ : Renames Kripke
  renᵏ ι k κ = k (κ ∘ˢ ι)

  _[_]ᵏ : ∀ {n} -> Kripke n -> Fam n -> Fam n
  k [ t ]ᵏ = k stop t

  _∘ᵏ_ : ∀ {n} -> Kripke n -> Kripke n -> Kripke n
  (k₂ ∘ᵏ k₁) ι = k₂ ι ∘ k₁ ι

record Context (Fam : ℕ -> Set) : Set where
  infixl 5 _▻_

  field ren : Renames Fam

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
open Context {{...}} public

Unrenames : (ℕ -> Set) -> Set
Unrenames Fam = ∀ {n m} -> n ⊑ m -> Fam m -> Maybe (Fam n)

record Backwards (Fam : ℕ -> Set) : Set where
  field unren : Unrenames Fam

  unshift : ∀ {n} -> Fam (suc n) -> Maybe (Fam n)
  unshift = unren top
open Backwards {{...}} public

record Environment Fam {{context : Context Fam}} : Set where
  infix  4 _↤_
  infixl 5 _▷_

  open Kripke Fam

  field fresh : ∀ {n} -> Fam (suc n)

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






-- {-# BUILTIN REWRITE _≡_ #-}

-- {-record Abstractable (Fam : ℕ -> Set) : Set where
--   open Kripke Fam

--   field abstᵏ : ∀ {n} -> Fam (suc n) -> Kripke n

--   postulate instᵏ-abstᵏ : ∀ {{c : Context Fam}} {{_ : Environment Fam}} {n}
--                         -> {t : Fam (suc n)} -> abstᵏ t top fresh ≡ t

--   {-# REWRITE instᵏ-abstᵏ #-}
-- open Abstractable {{...}} public-}

-- {-data Abstractable (Fam : ℕ -> Set) : Set where
--   abstᵏ : let open Kripke Fam in
--             (∀ {n} -> Fam (suc n) -> Kripke n) -> Abstractable Fam

-- unabst : ∀ {Fam} -> Abstractable Fam -> let open Kripke Fam in
--             ∀ {n} -> Fam (suc n) -> Kripke n
-- unabst (abstᵏ k) = k

-- postulate
--   instᵏ-abstᵏ : ∀ {Fam} {{c : Context Fam}} {{_ : Environment Fam}} {{v : Abstractable Fam}} {n}
--               -> {t : Fam (suc n)} -> unabst v t top fresh ≡ t

-- {-# REWRITE instᵏ-abstᵏ #-}-}
-- -- open Abstractable {{...}} public
