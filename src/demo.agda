-- This file contains a few concrete examples of both combinatory logic terms and λ-terms
-- as well as applications of proved results

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

------------------------
-- Playing with types --
------------------------
open import types

A : Type
A = X 0

B : Type
B = X 1

Γ : Ctx
Γ = Ø , A , B , A

---------------------------
-- Playing with CL-terms --
---------------------------
module cl-demo where
    open import combinatory-logic

    -- Iu ↠₁ u (generic)
    Iu-red : ∀ {Γ C} {u : Γ ⊢ C} → I · u ↠₁ u
    Iu-red = ↠₁I

    -- Variable x : A (specific)
    x : Γ ⊢ A
    x = var (suc (suc zero))

    -- Variable y : B (specific)
    y : Γ ⊢ B
    y = var (suc zero)

    -- Kxy (specific)
    Kxy : Γ ⊢ A
    Kxy = K · x · y

    -- Kxy ↠₁ x (specific)
    Kxy-red : Kxy ↠₁ x
    Kxy-red = ↠₁K

    -- [z].z (generic)
    id : ∀ {Γ C} → Γ ⊢ C ⇒ C
    id = abs (var zero)

    -- [z].y (semi-specific)
    ky : ∀ {C} → Γ ⊢ C ⇒ B
    ky = abs (wk-last y)
    
    -- ([z].y)u ↠ y (semi-specific)
    kyu-red : ∀ {C} {u : Γ ⊢ C} → ky · u ↠ y
    kyu-red {u = u} = red-th (wk-last y) u 

    -- [u].Ku (generic)
    skki : ∀ {C D} → Γ ⊢ C ⇒ D ⇒ C
    skki = abs (K · var zero)

    -- ([u].Ku)xy ↠ x (specific)
    skki-red : skki · x · y ↠ x
    skki-red = trans-↠ (↠l (red-th (abs (var (suc zero))) x) y) (red-th (wk-last x) y)

--------------------------
-- Playing with λ-terms --
--------------------------
module λ-demo where
    open import lambda-calculus

    -- Identity (generic)
    I : ∀ {Γ C} → Γ † C ⇒ C
    I = abs var zero

    -- Im ↝₁ m (generic)
    Im-red : ∀ {Γ C} {m : Γ † C} → I · m ↝₁ m
    Im-red {m = m} = ↝₁β (var zero) m

    -- Variable x : A (specific)
    x : Γ † A
    x = var (suc (suc zero))

    -- Variable y : B (specific)
    y : Γ † B
    y = var (suc zero)

    -- Kxy (specific)
    Kxy : Γ † A
    Kxy = (abs (abs var (suc zero))) · x · y

    -- Kxy ↝ x (specific)
    Kxy-red : Kxy ↝ x
    Kxy-red = trans-↝ (↝l (↝₁β (abs var (suc zero)) x ◅ ε) y) (↝₁β (wk-last x) y ◅ ε)
