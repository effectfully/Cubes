module Cubes.Test.Path where

open import Cubes.Typecheck

funExt : Term⁺
funExt = (pi type λ A
       → pi type λ B
       → pi (A ⇒ B) λ f
       → pi (A ⇒ B) λ g
       → (pi A λ x → path (ƛ B) (f · x) (g · x))
       ⇒ path (ƛ A ⇒ B) f g)
       ∋ lam 5 λ A B f g p → dim λ i → lam 1 λ x → p · x # i

congp : Term⁺
congp = (pi type λ A
      → pi type λ B
      → pi (A ⇒ B) λ f
      → pi A λ x
      → pi A λ y
      → path (ƛ A) x y
      ⇒ path (ƛ B) (f · x) (f · y))
      ∋ lam 6 λ A B f x y p → dim λ i → f · (p # i)

substp : Term⁺
substp = (pi type λ A
       → pi (A ⇒ type) λ B
       → pi A λ x
       → pi A λ y
       → path (ƛ A) x y
       ⇒ B · x
       ⇒ B · y)
       ∋ lam 6 λ A B x y p z → coe (lam 1 λ i → B · (p # i)) r z
