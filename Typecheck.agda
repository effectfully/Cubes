{-# OPTIONS --no-termination-check #-}

module Cubes.Typecheck where

open import Cubes.Core public

infix  4 _⊢_
infixl 8 _⟦_⟧ᵏ
infixl 2 _∋_

mutual
  data _⊢_ {n} (Γ : Con n) : Value n -> Set where
    intᵗ     : Γ ⊢ typeᵛ
    typeᵗ    : Γ ⊢ typeᵛ
    πᵗ       :  (σₜ : Γ           ⊢ typeᵛ)
             ->       Γ ▻ eval σₜ ⊢ typeᵛ
             ->       Γ           ⊢ typeᵛ
    pathᵗ    :  (σₜ : Γ ⊢ typeᵛ)
             ->       Γ ⊢ eval σₜ
             ->       Γ ⊢ eval σₜ
             ->       Γ ⊢ typeᵛ
    lᵗ       : Γ ⊢ intᵛ
    rᵗ       : Γ ⊢ intᵛ
    invᵗ     : Γ ⊢ intᵛ -> Γ ⊢ intᵛ
    varᵗ     : ∀ v -> Γ ⊢ lookupᶜ v Γ
    ƛᵗ       : ∀ {σ} {τₖ : Kripke n}
             -> Γ ▻ σ ⊢ instᵏ τₖ
             -> Γ     ⊢ piᵛ σ τₖ
    δᵗ       : ∀ {σ}
             -> (xₜ : Γ ▻ intᵛ ⊢ shift σ)
             ->       Γ        ⊢ pathᵛ σ ⟦ xₜ ⟧[ lᵛ ] ⟦ xₜ ⟧[ rᵛ ]
    _·ᵗ_     : ∀ {σ} {τₖ : Kripke n}
             ->       Γ ⊢ piᵛ σ τₖ
             -> (xₜ : Γ ⊢ σ)
             ->       Γ ⊢ τₖ ⟦ xₜ ⟧ᵏ
    _#ᵗ_     : ∀ {σ} {xₜ₁ : Γ ⊢ σ} {xₜ₂ : Γ ⊢ σ}
             ->       Γ ⊢ pathᵛ σ (eval xₜ₁) (eval xₜ₂)
             -> (iₜ : Γ ⊢ intᵛ)
             ->       Γ ⊢ σ
    coeᵗ     :  (τₜ : Γ ⊢ intᵛ ⇒ᵛ typeᵛ)
             -> (jₜ : Γ ⊢ intᵛ)
             ->       Γ ⊢ eval τₜ $ᵛ lᵛ
             ->       Γ ⊢ eval τₜ $ᵛ eval jₜ
    qcoerceᵗ : ∀ {σ τ} -> quoteᵛ₀ σ ≡ quoteᵛ₀ τ -> Γ ⊢ σ -> Γ ⊢ τ
    wkᵗ      : ∀ {σ} -> ε ⊢ σ -> Γ ⊢ wk₀ σ

  ⟦_/_⟧ : ∀ {n m σ} {Γ : Con n} -> m ↤ n -> Γ ⊢ σ -> Value m
  ⟦ ρ / intᵗ          ⟧ = intᵛ
  ⟦ ρ / typeᵗ         ⟧ = typeᵛ
  ⟦ ρ / πᵗ σ τ        ⟧ = piᵛ ⟦ ρ / σ ⟧ ⟦ ρ / τ ⟧ᵏ
  ⟦ ρ / pathᵗ σ x₁ x₂ ⟧ = pathᵛ ⟦ ρ / σ ⟧ ⟦ ρ / x₁ ⟧ ⟦ ρ / x₂ ⟧
  ⟦ ρ / lᵗ            ⟧ = lᵛ
  ⟦ ρ / rᵗ            ⟧ = rᵛ
  ⟦ ρ / invᵗ i        ⟧ = invertᵛ ⟦ ρ / i ⟧
  ⟦ ρ / varᵗ v        ⟧ = lookupᵉ v ρ
  ⟦ ρ / ƛᵗ b          ⟧ = lamᵛ ⟦ ρ / b ⟧ᵏ
  ⟦ ρ / δᵗ x          ⟧ = dimᵛ ⟦ ρ / x ⟧ᵏ
  ⟦ ρ / f ·ᵗ x        ⟧ = ⟦ ρ / f ⟧ $ᵛ ⟦ ρ / x ⟧
  ⟦ ρ / p #ᵗ i        ⟧ = ⟦ ρ / p ⟧# ⟦ ρ / i ⟧
  ⟦ ρ / coeᵗ τ j x    ⟧ = let ⟦τ⟧ , ⟦x⟧ , ⟦j⟧ = ⟦ ρ / τ ⟧ , ⟦ ρ / x ⟧ , ⟦ ρ / j ⟧ in
    if quoteᵛ ⟦j⟧ == Pure.l ∨ isConstᵛ ⟦τ⟧ then ⟦x⟧ else coeᵛ ⟦τ⟧ ⟦x⟧ ⟦j⟧
  ⟦ ρ / qcoerceᵗ q t  ⟧ = ⟦ ρ / t ⟧
  ⟦ ρ / wkᵗ t         ⟧ = wk₀ (eval t)

  ⟦_/_⟧ᵏ : ∀ {n m σ τ} {Γ : Con n} -> m ↤ n -> Γ ▻ σ ⊢ τ -> Kripke m
  ⟦ ρ / b ⟧ᵏ ι x = ⟦ renᵉ ι ρ ▷ x / b ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value n
  eval = ⟦ stopᵉ /_⟧

  ⟦_/_⟧#_ : ∀ {n m Γ σ} {xₜ₁ : Γ ⊢ σ} {xₜ₂ : Γ ⊢ σ}
          -> m ↤ n -> Γ ⊢ pathᵛ σ (eval xₜ₁) (eval xₜ₂) -> Value m -> Value m
  ⟦_/_⟧#_ {xₜ₁ = xₜ₁} ρ p lᵛ = ⟦ ρ / xₜ₁ ⟧
  ⟦_/_⟧#_ {xₜ₂ = xₜ₂} ρ p rᵛ = ⟦ ρ / xₜ₂ ⟧
  ⟦ ρ / p ⟧# iᵥ = case ⟦ ρ / p ⟧ of λ
    { (dimᵛ xₖ) -> xₖ [ iᵥ ]ᵏ
    ;  pᵥ       -> pᵥ #ᵛ iᵥ
    }

  _⟦_⟧ᵏ : ∀ {n σ} {Γ : Con n} -> Kripke n -> Γ ⊢ σ -> Value n
  k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

  ⟦_⟧[_] : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Value n -> Value n
  ⟦ b ⟧[ x ] = ⟦ stopᵉ ▷ x / b ⟧

  ⟦_⟧⟦_⟧ : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Value n
  ⟦ b ⟧⟦ x ⟧ = ⟦ b ⟧[ eval x ]

pattern _#⟨_,_⟩ᵗ_ p x₁ x₂ i = _#ᵗ_ {xₜ₁ = x₁} {xₜ₂ = x₂} p i

module _ {A} where
  open TermWith A

  erase : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Term n
  erase  intᵗ           = int
  erase  typeᵗ          = type
  erase (πᵗ σ τ)        = π (erase σ) (erase τ)
  erase (pathᵗ σ x₁ x₂) = path (erase σ) (erase x₁) (erase x₂)
  erase  lᵗ             = l
  erase  rᵗ             = r
  erase (invᵗ i)        = inv (erase i)
  erase (varᵗ v)        = var v
  erase (ƛᵗ b)          = ƛ (erase b)
  erase (δᵗ x)          = δ (erase x)
  erase (f ·ᵗ x)        = erase f · erase x
  erase (p #ᵗ i)        = erase p # erase i
  erase (coeᵗ σ j x)    = coe (erase σ) (erase j) (erase x)
  erase (qcoerceᵗ q t)  = erase t
  erase (wkᵗ t)         = wk₀ (erase t)

Typed : Set
Typed = ∃ λ (σ⁺ : Value⁺) -> ∀ {n} {Γ : Con n} -> Γ ⊢ σ⁺

open TermWith Typed public

data NonInferable : Set where
  ƛₙᵢ δₙᵢ : NonInferable

data TCError : Set where
  mismatch     : ∀ {n} -> Pure n -> Pure n -> Term n -> TCError
  nonInferable : NonInferable -> TCError
  nonFunction  : ∀ {n} -> Term n -> TCError
  nonPath      : ∀ {n} -> Term n -> TCError

instance
  ⊢Show : ∀ {n σ} {Γ : Con n} -> Show (Γ ⊢ σ)
  ⊢Show = record { show = show ∘ erase {⊥} }

  typedShow : Show Typed
  typedShow = record { show = λ p -> show (proj₂ p {Γ = ε}) }

  nonInferableShow : Show NonInferable
  nonInferableShow = record { show = λ{ ƛₙᵢ -> "ƛ" ; δₙᵢ -> "δ" } }

  tcErrorShow : Show TCError
  tcErrorShow = record
    { show = λ
        { (mismatch σᵢ σₑ t) ->  "the expected type of "
                             s++ showCode t
                             s++ " is "
                             s++ showCode σᵢ
                             s++ " but got "
                             s++ showCode σₑ
        ; (nonInferable ni)  -> "can't infer the type of " s++ show ni
        ; (nonFunction t)    -> showCode t s++ " is not a function"
        ; (nonPath t)        -> showCode t s++ " is not a path"
        }
    }

TCM : Set -> Set
TCM A = TCError ⊎ A

throw : ∀ {A} -> TCError -> TCM A
throw = inj₁

coerceᵗ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> TCM (Γ ⊢ τ)
coerceᵗ {σ = σ} {τ} t =
  maybeToSum (mismatch qσ qτ (erase t)) $ flip qcoerceᵗ t <$> qσ ≟ qτ where
    qσ = quoteᵛ₀ σ
    qτ = quoteᵛ₀ τ

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> TCM (∃ (Γ ⊢_))
  infer (pure (, tₜ⁺)) = return (, tₜ⁺)
  infer  int           = return (, intᵗ)
  infer  type          = return (, typeᵗ)
  infer (π σ τ)        = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , πᵗ σₜ τₜ) <$> check τ typeᵛ
  infer (path σ x₁ x₂) = check σ typeᵛ >>= λ σₜ ->
    (λ xₜ₁ xₜ₂ -> , pathᵗ σₜ xₜ₁ xₜ₂) <$> check x₁ (eval σₜ) ⊛ check x₂ (eval σₜ)
  infer  l             = return (, lᵗ)
  infer  r             = return (, rᵗ)
  infer (inv i)        = (λ iₜ -> , invᵗ iₜ) <$> check i intᵛ
  infer (var v)        = return (, varᵗ v)
  infer (ƛ b)          = throw $ nonInferable ƛₙᵢ
  infer (δ x)          = throw $ nonInferable δₙᵢ -- Well...
  infer (f · x)        = infer f >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _              -> throw $ nonFunction f
    }
  infer (p # i)        = infer p >>= λ
    { (pathᵛ σ x₁ x₂ , pₜ) ->
         check (quoteᵛ x₁) σ >>= λ xₜ₁ ->
         check (quoteᵛ x₂) σ >>= λ xₜ₂ ->
           (λ iₜ pₜ′ -> , pₜ′ #⟨ xₜ₁ , xₜ₂ ⟩ᵗ iₜ) <$> check i intᵛ ⊛ coerceᵗ pₜ
    ;  _                   -> throw $ nonPath p
    }
  infer (coe τ j x)    = check τ (intᵛ ⇒ᵛ typeᵛ) >>= λ τₜ ->
    (λ jₜ xₜ -> , coeᵗ τₜ jₜ xₜ) <$> check j intᵛ ⊛ check x (eval τₜ $ᵛ lᵛ)

  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value n) -> TCM (Γ ⊢ σ)
  check (ƛ b)   (piᵛ σ τₖ)      = ƛᵗ <$> check b (instᵏ τₖ)
  check (δ x)   (pathᵛ σ x₁ x₂) = check x (shift σ) >>= coerceᵗ ∘ δᵗ
  check  t       σ              = infer t >>= coerceᵗ ∘ proj₂

typecheck : Term⁽⁾ -> Value⁽⁾ -> TCM Term⁺
typecheck t σ = (λ tₜ {_} -> pure $ wk₀ σ , wkᵗ tₜ) <$> check t σ 

_∋_ : ∀ σ t -> _
σ ∋ t = left show (check {Γ = ε} σ typeᵛ) >>=ᵗ λ σₜ -> left show (typecheck t (eval σₜ)) >>=ᵗ id
