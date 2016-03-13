module Cubes.Test.Path where

open import Cubes.Typecheck

funExt : Term⁺
funExt = (pi type λ A
       → pi type λ B
       → pi (A ⇒ B) λ f
       → pi (A ⇒ B) λ g
       → (pi A λ x → path B (f · x) (g · x))
       ⇒ path (A ⇒ B) f g)
       ∋ lam 5 λ A B f g p → dim λ i → lam 1 λ x → p · x # i

pcong : Term⁺
pcong = (pi type λ A
      → pi type λ B
      → pi (A ⇒ B) λ f
      → pi A λ x
      → pi A λ y
      → path A x y
      ⇒ path B (f · x) (f · y))
      ∋ lam 6 λ A B f x y p → dim λ i → f · (p # i)

psubst : Term⁺
psubst = (pi type λ A
       → pi (A ⇒ type) λ B
       → pi A λ x
       → pi A λ y
       → path A x y
       ⇒ B · x
       ⇒ B · y)
       ∋ lam 6 λ A B x y p z → coe (lam 1 λ i → B · (p # i)) r z

idp : Term⁺
idp = (pi type λ A → pi A λ x → path A x x)
    ∋ lam 2 λ A x → dim λ i → x 

li : Term⁺
li = (pi int λ i → path int l i)
   ∋ lam 1 λ i → coe (lam 1 λ i → path int l i) i (idp · int · l)

psqueeze : Term⁺
psqueeze = (pi type λ A
         → pi A λ x
         → pi A λ y
         → pi int λ i
         → pi (path A x y) λ p
         → path A x (p # (li · r # i)))
         ∋ lam 5 λ A x y i p → dim λ j → p # (li · j # i)

J : Term⁺
J = (pi type λ A
  → pi A λ x
  → pi A λ y
  → pi (pi A λ y → path A x y ⇒ type) λ B
  → B · x · (idp · A · x)
  ⇒ pi (path A x y) λ p
  → B · y · p)
  ∋ lam 6 λ A x y B z p →
      coe (lam 1 λ i → B · (p # (li · r # i)) · (psqueeze · A · x · y · i · p)) r z
