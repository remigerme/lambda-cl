open import types
open import combinatory-logic renaming (abs to abs-cl; wk-last to wk-last-cl) 
open import lambda-calculus

-- From λ to CL
λcl : ∀ {Γ A} → Γ † A → Γ ⊢ A
λcl (var x) = var x
λcl (m · n) = λcl m · λcl n
λcl (abs m) = abs-cl (λcl m)

-- From CL to λ
clλ : ∀ {Γ A} → Γ ⊢ A → Γ † A
clλ (var x) = var x
clλ (u · v) = (clλ u) · (clλ v)
clλ I = abs (var zero)
clλ K = abs (abs (var (suc zero)))
clλ S = abs (abs (abs ((var (suc (suc zero)) · var zero · (var (suc zero) · var zero)))))
