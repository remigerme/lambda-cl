open import Types

data _⊢_ : Ctx → Type → Set where
    var : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
    _·_ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    abs_ : ∀ {Γ A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
