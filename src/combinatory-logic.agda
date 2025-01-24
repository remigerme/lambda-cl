open import Types

data _⊢_ : Ctx → Type → Set where
    var : ∀ {Γ A}     → Γ ∋ A       → Γ ⊢ A
    _·_ : ∀ {Γ A B}   → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    I   : ∀ {Γ A}                   → Γ ⊢ (A ⇒ A)
    K   : ∀ {Γ A B}                 → Γ ⊢ (A ⇒ (B ⇒ A))
    S   : ∀ {Γ A B C}               → Γ ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))

data _↝_ : {Γ : Ctx} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where
    ↝l : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} → t ↝ t' → (u : Γ ⊢ A)                 → (t · u) ↝ (t' · u)
    ↝r : ∀ {Γ A B} (t : Γ ⊢ (A ⇒ B)) → {u u' : Γ ⊢ A} → u ↝ u'                 → (t · u) ↝ (t · u')
    ↝I : ∀ {Γ A} (t : Γ ⊢ A)                                                   → (I · t) ↝ t
    ↝K : ∀ {Γ A B} (t : Γ ⊢ A) → (u : Γ ⊢ B)                                   → ((K · t) · u) ↝ t
    ↝S : ∀ {Γ A B C} (t : Γ ⊢ (A ⇒ (B ⇒ C))) → (u : Γ ⊢ (A ⇒ B)) → (v : Γ ⊢ A) → (((S · t) · u) · v) ↝ ((t · v) · (u · v))


-- A basic test manipulating defs
A : Type
A = X 0

Γ : Ctx
Γ = Ø , A

term : Γ ⊢ A
term = I · var zero

rterm : Γ ⊢ A
rterm = var zero

red : term ↝ rterm
red = ↝I rterm
