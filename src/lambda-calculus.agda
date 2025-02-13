module lambda-calculus where

open import types

data _†_ : Ctx → Type → Set where
    var  : ∀ {Γ A} → Γ ∋ A               → Γ † A
    _·_  : ∀ {Γ A B} → Γ † A ⇒ B → Γ † A → Γ † B
    abs_ : ∀ {Γ A B} → Γ , A † B         → Γ † A ⇒ B

wk : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ † A → Δ † A
wk p (var x) = var (wk-var p x)
wk p (t · u) = wk p t · wk p u
wk p (abs t) = abs wk (keep p) t

wk-last : ∀ {Γ A B} → Γ † A → Γ , B † A
wk-last t = wk (drop ⊆-refl) t
