open import Types

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)

-- Typed CL terms
data _⊢_ : Ctx → Type → Set where
    var : ∀ {Γ A}     → Γ ∋ A       → Γ ⊢ A
    _·_ : ∀ {Γ A B}   → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    I   : ∀ {Γ A}                   → Γ ⊢ (A ⇒ A)
    K   : ∀ {Γ A B}                 → Γ ⊢ (A ⇒ (B ⇒ A))
    S   : ∀ {Γ A B C}               → Γ ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))

-- Weak reduction
data _↝_ : {Γ : Ctx} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where
    ↝l : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} → t ↝ t' → (u : Γ ⊢ A)                 → (t · u) ↝ (t' · u)
    ↝r : ∀ {Γ A B} (t : Γ ⊢ (A ⇒ B)) → {u u' : Γ ⊢ A} → u ↝ u'                 → (t · u) ↝ (t · u')
    ↝I : ∀ {Γ A} {t : Γ ⊢ A}                                                   → (I · t) ↝ t
    ↝K : ∀ {Γ A B} {t : Γ ⊢ A} → {u : Γ ⊢ B}                                   → ((K · t) · u) ↝ t
    ↝S : ∀ {Γ A B C} {t : Γ ⊢ (A ⇒ (B ⇒ C))} → {u : Γ ⊢ (A ⇒ B)} → {v : Γ ⊢ A} → (((S · t) · u) · v) ↝ ((t · v) · (u · v))

data Result (A : Set) : Set where
    done : A → Result A
    fail : Result A

-- Determine wether two variables are the exact same or not
_=-var_ : {Γ : Ctx} {A B : Type} → Γ ∋ A → Γ ∋ B → Result (A ≡ B)
zero =-var zero = done refl -- same variables so same types
zero =-var suc y = fail -- not the same variables, can't say anything on types
suc x =-var zero = fail -- not the same variables, can't say anything on types
suc x =-var suc y = x =-var y

-- Is it a good idea / approach ?
tm-type-lem : {Γ : Ctx} {A B : Type} → Γ ⊢ A → A ≡ B → Γ ⊢ B
tm-type-lem {Γ} t eq = subst (λ T → Γ ⊢ T) eq t

abs : {Γ : Ctx} {A B : Type} → Γ ∋ A → Γ ⊢ B → Γ ⊢ (A ⇒ B)
abs {Γ} {A} x (var y) with x =-var y
... | done eq = tm-type-lem I (cong (λ b → A ⇒ b) eq)
... | fail    = K · (var y)
abs x (t · u) = (S · (abs x t)) · (abs x u)
abs x I       = K · I
abs x K       = K · K
abs x S       = K · S

_[_/_] : {Γ : Ctx} {A B : Type} → Γ ⊢ A → Γ ⊢ B → Γ ∋ B → Γ ⊢ A
var y [ u / x ] with x =-var y
... | done eq = tm-type-lem u eq
... | fail = var y
(t · t') [ u / x ] = (t [ u / x ]) · (t' [ u / x ])
I [ u / x ] = I
K [ u / x ] = K
S [ u / x ] = S

trans-↝ : {Γ : Ctx} {A : Type} {u v w : Γ ⊢ A} → u ↝ v → v ↝ w → u ↝ w
trans-↝ (↝l r1 u) r2 = {!   !}
trans-↝ (↝r t r1) r2 = {!   !}
trans-↝ ↝I r2 = {!   !}
trans-↝ ↝K r2 = {!   !}
trans-↝ ↝S r2 = {!   !}

red-th : {Γ : Ctx} {A B : Type} {x : Γ ∋ A} {t : Γ ⊢ B} {u : Γ ⊢ A} → ((abs x t) · u) ↝ (t [ u / x ])
red-th {Γ} {A} {B} {x} {t} {u} with t
... | s · s' = trans-↝ ↝S (trans-↝ (↝l (red-th {t = s} ) (abs x s' · u)) (↝r (s [ u / x ]) red-th))
    -- abs x (s · s') · u ↝  (abs x s · u) · (abs x s' · u) by ↝S
    -- abs x s · u ↝ s [ u / x ] thanks to red-th
    -- abs x s' · u ↝ s' [ u / x ] thanks to red-th
    -- abs x (s · s') · u ↝ (s [ u / x ]) · (s' [ u / x ]) by trans
... | I = ↝K
... | K = ↝K
... | S = ↝K
... | var y with x =-var y
...     | done refl = ↝I
...     | fail = ↝K


-- Basic tests manipulating defs
A : Type
A = X 0

Γ : Ctx
Γ = (Ø , A) , A

-- Testing reduction
-- Ix
term : Γ ⊢ A
term = I · var zero

-- x
rterm : Γ ⊢ A
rterm = var zero

-- Ix ↝ x
red : term ↝ rterm
red = ↝I

-- Kxy
termb : Γ ⊢ A
termb = (K · var zero) · (var (suc zero))

-- Kxy ↝ x
redb : termb ↝ rterm
redb = ↝K

-- Testing abstraction
-- [x].x
id : Γ ⊢ (A ⇒ A)
id = abs zero (var zero)

-- [x].y
k : Γ ⊢ (A ⇒ A)
k = abs (suc zero) (var zero)

-- [x].Kx
skki : {B : Type} → Γ ⊢ (A ⇒ (B ⇒ A))
skki = abs zero (K · var zero)
