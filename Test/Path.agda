module Cubes.Test.Path where

open import Cubes.Typecheck

FunExt : Type⁽⁾
FunExt = pi type λ A
       → pi type λ B
       → pi (A ⇒ B) λ f
       → pi (A ⇒ B) λ g
       → (pi A λ x → path B (f · x) (g · x))
       ⇒ path (A ⇒ B) f g

funExt : Term⁽⁾
funExt = lam 5 λ A B f g p → dim λ i → lam 1 λ x → p · x # i

funExt-∈-FunExt : funExt ∈ FunExt
funExt-∈-FunExt = tt

Congp : Type⁽⁾
Congp = pi type λ A
      → pi type λ B
      → pi (A ⇒ B) λ f
      → pi A λ x
      → pi A λ y
      → path A x y
      ⇒ path B (f · x) (f · y)

congp : Term⁽⁾
congp = lam 6 λ A B f x y p → dim λ i → f · (p # i)

congp-∈-Congp : congp ∈ Congp
congp-∈-Congp = tt

Substp : Type⁽⁾
Substp = pi type λ A
       → pi (A ⇒ type) λ B
       → pi A λ x
       → pi A λ y
       → path A x y
       ⇒ B · x
       ⇒ B · y

substp : Term⁽⁾
substp = lam 6 λ A B x y p z → bcoe (λ i → B · (p # i)) r z

substp-∈-Substp : substp ∈ Substp
substp-∈-Substp = tt
