module Cubes.Test where

open import Cubes.Core
open import Cubes.Typecheck

A : Term⁺
A = ƛ ƛ ƛ ƛ var (fsuc fzero) · var fzero

Aᵗ : Term⁺
Aᵗ = π type                                                  $
     π (π (var fzero) type)                                  $
     π (π (var (fsuc fzero)) $ var (fsuc fzero) · var fzero) $
     π (var (fsuc (fsuc fzero)))                             $
     var (fsuc (fsuc fzero)) · var fzero

Aᵀ : T (A ∈? Aᵗ)
Aᵀ = _

-- (typecheck A Aᵗ) evaluates to
-- ƛᵗ (ƛᵗ (ƛᵗ (ƛᵗ (qcoerceᵗ refl (varᵗ (fsuc fzero) ·ᵗ qcoerceᵗ refl (varᵗ fzero))))))
