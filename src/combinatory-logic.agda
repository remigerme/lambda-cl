module combinatory-logic where

open import types

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)

-- Typed CL terms
data _⊢_ : Ctx → Type → Set where
    var : ∀ {Γ A}     → Γ ∋ A     → Γ ⊢ A
    _·_ : ∀ {Γ A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    I   : ∀ {Γ A}                 → Γ ⊢ A ⇒ A
    K   : ∀ {Γ A B}               → Γ ⊢ A ⇒ (B ⇒ A)
    S   : ∀ {Γ A B C}             → Γ ⊢ (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))

infixl 30 _·_
infix 10 _⊢_

wk : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
wk p (var x) = var (wk-var p x)
wk p (t · u) = wk p t · wk p u
wk p I       = I
wk p K       = K
wk p S       = S

wk-last : ∀ {Γ A B} → Γ ⊢ A → Γ , B ⊢ A
wk-last t = wk (drop ⊆-refl) t

-- Weak reduction : one step
data _↠₁_ : {Γ : Ctx} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where
    ↠₁l : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} → t ↠₁ t' → (u : Γ ⊢ A)                → (t · u) ↠₁ (t' · u)
    ↠₁r : ∀ {Γ A B} (t : Γ ⊢ (A ⇒ B)) → {u u' : Γ ⊢ A} → u ↠₁ u'                → (t · u) ↠₁ (t · u')
    ↠₁I : ∀ {Γ A} {t : Γ ⊢ A}                                                   → (I · t) ↠₁ t
    ↠₁K : ∀ {Γ A B} {t : Γ ⊢ A} → {u : Γ ⊢ B}                                   → ((K · t) · u) ↠₁ t
    ↠₁S : ∀ {Γ A B C} {t : Γ ⊢ (A ⇒ (B ⇒ C))} → {u : Γ ⊢ (A ⇒ B)} → {v : Γ ⊢ A} → (((S · t) · u) · v) ↠₁ ((t · v) · (u · v))

-- Weak reduction : multiple steps
_↠_ : {Γ : Ctx} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set
_↠_ = Star _↠₁_

-- Defining shortcuts for convenience
↠l : ∀ {Γ A B} {t t' : Γ ⊢ (A ⇒ B)} → t ↠ t' → (u : Γ ⊢ A) → (t · u) ↠ (t' · u)
↠l ε u = ε
↠l (x ◅ r) u = ↠₁l x u ◅ ↠l r u

↠r : ∀ {Γ A B} (t : Γ ⊢ (A ⇒ B)) → {u u' : Γ ⊢ A} → u ↠ u' → (t · u) ↠ (t · u')
↠r t ε = ε
↠r t (x ◅ r) = ↠₁r t x ◅ ↠r t r

↠I : ∀ {Γ A} {t : Γ ⊢ A} → (I · t) ↠ t
↠I = ε ▻ ↠₁I

↠K : ∀ {Γ A B} {t : Γ ⊢ A} {u : Γ ⊢ B} → ((K · t) · u) ↠ t
↠K = ε ▻ ↠₁K

↠S : ∀ {Γ A B C} {t : Γ ⊢ (A ⇒ (B ⇒ C))} → {u : Γ ⊢ (A ⇒ B)} → {v : Γ ⊢ A} → (((S · t) · u) · v) ↠ ((t · v) · (u · v))
↠S = ε ▻ ↠₁S

-- Now useless
tm-type-lem : {Γ : Ctx} {A B : Type} → Γ ⊢ A → A ≡ B → Γ ⊢ B
tm-type-lem {Γ} t eq = subst (λ T → Γ ⊢ T) eq t

abs : {Γ : Ctx} {A B : Type} → Γ , A ⊢ B → Γ ⊢ (A ⇒ B)
abs (var zero) = I
abs (var (suc x)) = K · var x
abs (t · u) = S · abs t · abs u
abs I = K · I
abs K = K · K
abs S = K · S

_[_] : ∀ {Γ Δ A} → Γ ⊢ A → (∀ {B} → Γ ∋ B → Δ ⊢ B) → Δ ⊢ A
var x [ σ ] = σ x
(t · u) [ σ ] = (t [ σ ]) · (u [ σ ])
I [ σ ] = I
K [ σ ] = K
S [ σ ] = S

_[_/0] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
t [ u /0] = t [ (λ { zero → u ; (suc x) → var x}) ] 

trans-↠ : {Γ : Ctx} {A : Type} {u v w : Γ ⊢ A} → u ↠ v → v ↠ w → u ↠ w
trans-↠ ε vw = vw
trans-↠ (x ◅ s) vw = x ◅ trans-↠ s vw

-- Reduction / substitution theorem
-- Details of the annoying case below
-- abs x (s · s') · u ↠  (abs x s · u) · (abs x s' · u) by ↠S
-- abs x s · u        ↠ s [ u / x ]                     by rec on red-th
-- abs x s' · u       ↠ s' [ u / x ]                    by rec on red-th
-- abs x (s · s') · u ↠ (s [ u / x ]) · (s' [ u / x ])  by trans
red-th' : {Γ : Ctx} {A B : Type} {t : Γ , A ⊢ B} {u : Γ ⊢ A} → ((abs t) · u) ↠ (t [ u /0])
red-th' {Γ} {A} {B} {t} {u} with t
... | var zero = ↠I
... | var (suc x) = ↠K
... | s · s' = trans-↠ ↠S (trans-↠ (↠l (red-th') (abs s' · u)) (↠r (s [ u /0]) red-th'))
... | I = ↠K
... | K = ↠K
... | S = ↠K

-- Basic tests manipulating defs
A : Type
A = X 0

Γ : Ctx
Γ = Ø , A , A

-- Testing reduction
-- Ix
term : Γ ⊢ A
term = I · var zero

-- x
rterm : Γ ⊢ A
rterm = var zero

-- Ix ↠₁ x
red : term ↠₁ rterm
red = ↠₁I

-- Kxy
termb : Γ ⊢ A
termb = K · var zero · var (suc zero)

-- Kxy ↠₁ x
redb : termb ↠₁ rterm
redb = ↠₁K

-- Testing abstraction
-- [x].x
id : Γ ⊢ (A ⇒ A)
id = abs (var zero)

-- [x].y
k : Γ ⊢ (A ⇒ A)
k = abs (var (suc zero))

-- [x].Kx
skki : {B : Type} → Γ ⊢ (A ⇒ (B ⇒ A))
skki = abs (K · var zero)
