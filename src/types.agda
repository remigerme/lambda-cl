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
