module Cubes.Test where

open import Cubes.Core
open import Cubes.Typecheck

A : Term⁺
A = lift $ lam 4 λ A B f x -> f · x

Aᵗ : Type⁺
Aᵗ = lift $ pi type λ A -> pi (A ~> type) λ B -> (pi A λ x -> B · x) ~> pi A λ x -> B · x

A∈Aᵗ : A ∈ Aᵗ
A∈Aᵗ = tt

-- (typecheck A Aᵗ) evaluates to
-- ƛᵗ (ƛᵗ (ƛᵗ (ƛᵗ (qcoerceᵗ refl (varᵗ (fsuc fzero) ·ᵗ qcoerceᵗ refl (varᵗ fzero))))))

FunExt : Type⁺
FunExt = lift $
  pi type λ A ->
  pi type λ B ->
  pi (A ~> B) λ f ->
  pi (A ~> B) λ g ->
  (pi A λ x -> path B (f · x) (g · x)) ~>
  path (A ~> B) f g

funExt : Term⁺
funExt = lift $ lam 5 λ A B f g p -> dim λ i -> lam 1 λ x -> p · x # i

funExt-∈-FunExt : funExt ∈ FunExt
funExt-∈-FunExt = tt
