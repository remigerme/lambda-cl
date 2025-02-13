module lambda-calculus where

open import types

data _†_ : Ctx → Type → Set where
    var  : ∀ {Γ A} → Γ ∋ A               → Γ † A
    _·_  : ∀ {Γ A B} → Γ † A ⇒ B → Γ † A → Γ † B
    abs_ : ∀ {Γ A B} → Γ , A † B         → Γ † A ⇒ B

data _⊆_ : Ctx → Ctx → Set where
    Ø⊆Ø  : Ø ⊆ Ø
    keep : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ , A ⊆ Δ , A
    drop : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ , A ⊆ Δ , A

infix 10 _⊆_
