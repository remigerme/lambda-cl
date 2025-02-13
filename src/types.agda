module types where

open import Data.Nat

-- We need an infinite number of distinct variables for types
-- Arbitrarily, these types variables will be integers behind the hood
TVar : Set
TVar = ℕ

data Type : Set where
    X   : TVar → Type
    _⇒_ : Type → Type → Type

infixr 40 _⇒_

data Ctx : Set where
    Ø   : Ctx
    _,_ : Ctx → Type → Ctx

infixl 40 _,_

data _∋_ : Ctx → Type → Set where
    zero : ∀ {Γ A}           → (Γ , A) ∋ A
    suc  : ∀ {Γ B A} → Γ ∋ A → (Γ , B) ∋ A

data _⊆_ : Ctx → Ctx → Set where
    Ø⊆Ø  : Ø ⊆ Ø
    keep : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ , A ⊆ Δ , A
    drop : ∀ {Γ Δ A} → Γ ⊆ Δ →     Γ ⊆ Δ , A

infix 10 _⊆_

⊆-refl : ∀ {Γ} → Γ ⊆ Γ
⊆-refl {Ø}     = Ø⊆Ø
⊆-refl {Γ , A} = keep ⊆-refl

wk-var : ∀ {Γ Δ A} → Γ ⊆ Δ → Γ ∋ A → Δ ∋ A
wk-var (keep p) zero    = zero
wk-var (keep p) (suc x) = suc (wk-var p x)
wk-var (drop p) x       = suc (wk-var p x)
