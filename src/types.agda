module Types where

open import Data.Nat

-- We need an infinite number of distinct variables for types
-- Arbitrarily, these types variables will be integers behind the hood
TVar : Set
TVar = ℕ

data Type : Set where
    X : TVar → Type
    _⇒_ : Type → Type → Type

data Ctx : Set where
    Ø : Ctx
    _,_ : Ctx → Type → Ctx

data _∋_ : Ctx → Type → Set where
    zero : ∀ {Γ A} → (Γ , A) ∋ A
    suc : ∀ {Γ B A} → Γ ∋ A → (Γ , B) ∋ A
