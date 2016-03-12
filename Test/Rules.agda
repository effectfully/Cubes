module Cubes.Test.Rules where

open import Cubes.Typecheck
open import Cubes.Test.Combinators

ƛβ : Term⁺
ƛβ = i · type · I ∋ i

coe-l : Term⁺
coe-l = (pi (int ⇒ type) λ A
      → pi (pi int λ i → A · i ⇒ type) λ B
      → (pi int λ j → pi (A · l) λ x → B · j · coe A j x)
      ⇒ pi (A · l) λ x
      → B · l · x)
      ∋ lam 3 λ A B f → f · l

coe-A : Term⁺
coe-A = (pi type λ A
      → pi (A ⇒ type) λ B
      → pi int λ j
      → pi A λ x
      → B · coe (ƛ A) j x
      ⇒ B · x)
      ∋ lam 5 λ A B j x y → y
