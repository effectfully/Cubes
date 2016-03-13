# Cubes

It's a type checker for a simple dependently typed language with an interval type, based on [1]. The type checking procedure is very similar to that of [4]: it's bidirectional and NbE-based, so we have raw terms and values, but since we're in a dependently typed setting, there are also typed terms indexed by values that represent types. E.g. typed Π-types are

```
data _⊢_ {n} (Γ : Con n) : Value n -> Set where
  πᵗ : (σₜ : Γ ⊢ typeᵛ) -> Γ ▻ eval σₜ ⊢ typeᵛ -> Γ ⊢ typeᵛ
  ...
```

That example demonstrates that evaluation is defined on typed terms, which is a great source of confidence that type checking terminates, because there is no evaluation defined on raw terms.

Type checking returns either a (rudimentary) error or a typed term, hence the type system is Church-like and all typing rules are just constructors of `_⊢_`. Unlike in [4] binders in `Value` have Kripke semantics, e.g.

```
data Value n where
  piᵛ  : Value  n -> Kripke n -> Value n
  lamᵛ : Kripke n -> Value  n
  ...
```

where `Kripke n = ∀ {m} -> n ⊑ m -> Value m -> Value m`.

The HoTT part consists of the interval type `int`, left and right points `l` and `r`, the `1-` operator spelled as `inv`, the type of paths `path`, path abstraction `δ` (all variables are represented as de Bruijn indices), path application `_#_` (Agda doesn't allow to use `_@_`) and `coe`. Everything is the same as in [1], except that `path` is the homogeneous `Path` from [2] and not `PathOver` (see [3]) and the order of arguments to `coe` is changed: it's `coe A j x` instead of `coe A x j`. No univalence and data types for now. All computational rules from [1] hold.

There is one another constructor of `Term`: `pure`. It's used to store typed terms in raw terms to prevent retypechecking.

## Examples

To define terms we use higher-order syntax in the style of [5].

Function extensionality is

```
funExt : Term⁺
funExt = (pi type λ A
       → pi type λ B
       → pi (A ⇒ B) λ f
       → pi (A ⇒ B) λ g
       → (pi A λ x → path B (f · x) (g · x))
       ⇒ path (A ⇒ B) f g)
       ∋ lam 5 λ A B f g p → dim λ i → lam 1 λ x → p · x # i
```

`_∋_` returns either a `String` with an error or a typed term wrapped in `pure`.

The definition of `J` is simplified version of the definition in [1]: `psqueeze` returns `path A x (p # squeeze i r))` rather than `path A x (p # i)` and we don't need `squeeze i r ~> i` (which causes all the trouble) to hold to define `J`.

```
idp : Term⁺
idp = (pi type λ A → pi A λ x → path A x x)
    ∋ lam 2 λ A x → dim λ i → x 

li : Term⁺
li = (pi int λ i → path int l i)
   ∋ lam 1 λ i → coe (lam 1 λ i → path int l i) i (idp · int · l)

squeeze : ∀ {n} -> Term n -> Term n -> Term n
squeeze i j = li · j # i

psqueeze : Term⁺
psqueeze = (pi type λ A
         → pi A λ x
         → pi A λ y
         → pi int λ i
         → pi (path A x y) λ p
         → path A x (p # squeeze i r))
         ∋ lam 5 λ A x y i p → dim λ j → p # squeeze i j

J : Term⁺
J = (pi type λ A
  → pi A λ x
  → pi A λ y
  → pi (pi A λ y → path A x y ⇒ type) λ B
  → B · x · (idp · A · x)
  ⇒ pi (path A x y) λ p
  → B · y · p)
  ∋ lam 6 λ A x y B z p →
      coe (lam 1 λ i → B · (p # squeeze i r) · (psqueeze · A · x · y · i · p)) r z
```

And `J` computes:

```
J-computes : Term⁺
J-computes = (pi type λ A
           → pi A λ x
           → pi (pi A λ y → path A x y ⇒ type) λ B
           → pi (B · x · (idp · A · x) ⇒ type) λ C
           → pi (B · x · (idp · A · x)) λ z
           → C · (J · A · x · x · B · z · (idp · A · x))
           ⇒ C ·  z)
           ∋ lam 6 λ A x B C z w → w
```

## References

[1] ["Homotopy Type Theory with an interval type"](https://valis.github.io/doc.pdf), Valery Isaev.

[2] ["Cubical Type Theory: a constructive interpretation of the univalence axiom"](https://www.math.ias.edu/~amortberg/papers/cubicaltt.pdf), Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg.

[3] ["A Cubical Approach to Synthetic Homotopy Theory"](http://dlicata.web.wesleyan.edu/pubs/lb15cubicalsynth/lb15cubicalsynth.pdf), Daniel R. Licata, Guillaume Brunerie.

[4] ["Simply Easy! An Implementation of a Dependently Typed Lambda Calculus"](http://strictlypositive.org/Easy.pdf), Andres Löh, Conor McBride, Wouter Swierstra.

[5] ["A little hack to make de Bruijn syntax more readable"](https://personal.cis.strath.ac.uk/conor.mcbride/fooling/Jigger.agda), Conor McBride.
