open import types
open import combinatory-logic renaming (abs to abs-cl; wk-last to wk-last-cl; red-th to red-th-cl) 
open import lambda-calculus

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

-- From λ to CL
λcl : ∀ {Γ A} → Γ † A → Γ ⊢ A
λcl (var x) = var x
λcl (m · n) = λcl m · λcl n
λcl (abs m) = abs-cl (λcl m)

-- From CL to λ
clλ : ∀ {Γ A} → Γ ⊢ A → Γ † A
clλ (var x) = var x
clλ (u · v) = clλ u · clλ v
clλ I = abs (var zero)
clλ K = abs (abs (var (suc zero)))
clλ S = abs (abs (abs ((var (suc (suc zero)) · var zero · (var (suc zero) · var zero)))))

--------------------
-- Results on clλ --
--------------------
 
-- Pre-lemma 9.5.a : handling one step of reduction in CL
clλ-↠₁ : ∀ {Γ A} {u v : Γ ⊢ A} → u ↠₁ v → clλ u ↝ clλ v
clλ-↠₁ (↠₁l e u) = ↝l (clλ-↠₁ e) (clλ u)
clλ-↠₁ (↠₁r t e) = ↝r (clλ t) (clλ-↠₁ e)
clλ-↠₁ {v = v} ↠₁I = red-th (var zero) (clλ v)
clλ-↠₁ {v = v} (↠₁K {u = u}) = trans-↝ (↝l (red-th (abs (var (suc zero))) (clλ v)) (clλ u)) {! red-th ? ?  !}
-- We now need to prove :
-- ((abs var (suc zero)) lambda-calculus.[ clλ v /0]) · clλ u ↝ clλ v
-- which I expected to prove by re-applying reduction theorem once again, but adga complains :'(
--
-- Previous sketch :
-- clλ-↠₁ {v = v} (↠₁K {u = u}) = trans-↝ ({! ↝₁β ? ?  !} ◅ ε) (red-th (var zero) (clλ v))
-- In hole above we need to prove
-- (abs (abs var (suc zero))) · clλ v · clλ u ↝ (abs var zero) · clλ v
-- where things are a bit reversed
-- note that I believe it to be intuitively the same problem as red-th-2 (from lambda-calculus.agda)
clλ-↠₁ ↠₁S = {!  !}

-- Lemma 9.5.a
clλ-↠ : ∀ {Γ A} {u v : Γ ⊢ A} → u ↠ v → clλ u ↝ clλ v
clλ-↠ ε = ε
clλ-↠ (x ◅ e) = trans-↝ (clλ-↠₁ x) (clλ-↠ e)

-- Lemma 9.5.b : clλ preserves weak equality
clλ-~ : ∀ {Γ A} {u v : Γ ⊢ A} → u ~ v → clλ u ≈ clλ v
clλ-~ (fwd x) = fwd (clλ-↠ x)
clλ-~ (bwd x) = bwd (clλ-↠ x)

-- Lemma 9.5.c : clλ preserves extensional equality
-- todo
 