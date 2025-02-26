module lambda-calculus where

open import types

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

data _†_ : Ctx → Type → Set where
    var  : ∀ {Γ A} → Γ ∋ A               → Γ † A
    _·_  : ∀ {Γ A B} → Γ † A ⇒ B → Γ † A → Γ † B
    abs_ : ∀ {Γ A B} → Γ , A † B         → Γ † A ⇒ B

infixl 30 _·_
infix 10 _†_

wk : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ † A → Δ † A
wk p (var x) = var (wk-var p x)
wk p (t · u) = wk p t · wk p u
wk p (abs t) = abs wk (keep p) t

wk-last : ∀ {Γ A B} → Γ † A → Γ , B † A
wk-last t = wk (drop ⊆-refl) t

_[_] : ∀ {Γ Δ A} → Γ † A → (∀ {B} → Γ ∋ B → Δ † B) → Δ † A
var x [ σ ]   = σ x
(t · u) [ σ ] = (t [ σ ]) · (u [ σ ])
(abs t) [ σ ] = abs (t [ (λ { zero → var zero ; (suc x) → wk-last (σ x)}) ]) 

_[_/0] : ∀ {Γ A B} → Γ , B † A → Γ † B → Γ † A
t [ u /0] = t [ (λ { zero → u ; (suc x) → var x}) ]

data _↝₁_ : ∀ {Γ A} → Γ † A → Γ † A → Set where
    ↝₁l : ∀ {Γ A B} {t t' : Γ † (A ⇒ B)} → t ↝₁ t' → (u : Γ † A) → (t · u) ↝₁ (t' · u)
    ↝₁r : ∀ {Γ A B} (t : Γ † (A ⇒ B)) → {u u' : Γ † A} → u ↝₁ u' → (t · u) ↝₁ (t · u')
    ↝₁λ : ∀ {Γ A B} {t t' : Γ , A † B} →                 t ↝₁ t' → (abs t) ↝₁ (abs t') 
    ↝₁β : ∀ {Γ A B} →              (t : Γ , A † B) → (u : Γ † A) → ((abs t) · u) ↝₁ ((t [ u /0]))
    ↝₁η : ∀ {Γ A B} →                            (u : Γ † A ⇒ B) → (abs (wk-last u · var zero)) ↝₁ u

_↝_ : ∀ {Γ A} → Γ † A → Γ † A → Set
_↝_ = Star _↝₁_

infix 10 _↝₁_
infix 10 _↝_

↝l : ∀ {Γ A B} {t t' : Γ † (A ⇒ B)} → t ↝ t' → (u : Γ † A) → t · u ↝ t' · u
↝l ε u = ε
↝l (x ◅ r) u = ↝₁l x u ◅ ↝l r u

↝r : ∀ {Γ A B} (t : Γ † (A ⇒ B)) → {u u' : Γ † A} → u ↝ u' → t · u ↝ t · u'
↝r t ε = ε
↝r t (x ◅ r) = ↝₁r t x ◅ ↝r t r

trans-↝ : ∀ {Γ A} {m n p : Γ † A} → m ↝ n → n ↝ p → m ↝ p
trans-↝ ε mp = mp
trans-↝ (x ◅ s) np = x ◅ trans-↝ s np

-- Reduction theorem (in fact the reduction is done in only one step)
red-th : ∀ {Γ A B} (m : Γ , A † B) → (n : Γ † A) → (abs m) · n ↝ m [ n /0]
red-th m n = ↝₁β m n ◅ ε

-- Reduction theorem : two steps in a row
-- red-th-2 : ∀ {Γ A B C} {m : Γ , A , B † C} {n : Γ † A} {p : Γ † B} → (abs (abs m)) · n · p ↝ ((wk ({!   !}) m [ wk-last n /0]) [ p /0])
-- red-th-2 = {!   !}
-- In order to even define the signature of this theorem we need to prove (in the hole)
-- Γ , A , B ⊆ Γ , B , A
-- which we expect to be true but is not trivial

ξ-proof : ∀ {Γ A B} → {t u : Γ , A † B} → t ↝ u → abs t ↝ abs u
ξ-proof ε = ε
ξ-proof (x ◅ p) = ↝₁λ x ◅ ξ-proof p

_≈_ : ∀ {Γ A} → Γ † A → Γ † A → Set
_≈_ = SymClosure _↝_
