import Mathlib

/-!
Partial formalization of equation (6.1): the envelope derivative.
The existence of the implicit critical point and all analytic hypotheses
are explicit inputs. No gamma-function or implicit-function theorem is
claimed to have been formalized here.
-/

namespace ConditionalSpectralAudit

/-- Differentiate the variational center along any differentiable branch
    satisfying the paper's critical-point identity at `κ`. -/
theorem center_hasDerivAt
    (lam s : ℝ → ℝ) (κ lam' s' : ℝ)
    (hlam : HasDerivAt lam lam' (s κ))
    (hs : HasDerivAt s s' κ)
    (hs0 : s κ ≠ 0)
    (hcritical : κ * (s κ * lam' - lam (s κ)) = 1) :
    HasDerivAt (fun x => (1 + x * lam (s x)) / s x)
      (lam (s κ) / s κ) κ := by
  have hc := hlam.comp κ hs
  have hn := (hasDerivAt_const κ (1 : ℝ)).add ((hasDerivAt_id κ).mul hc)
  have hd := hn.div hs hs0
  have hcancel : κ * s κ * lam' = 1 + κ * lam (s κ) := by nlinarith
  have heq :
      ((lam (s κ) + κ * (lam' * s')) * s κ -
        (1 + κ * lam (s κ)) * s') / s κ ^ 2 = lam (s κ) / s κ := by
    field_simp
    nlinarith [congrArg (fun y : ℝ => y * s') hcancel]
  convert hd using 1 <;>
    first
    | rfl
    | simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply,
        id_eq, zero_add, one_mul, heq]

#print axioms center_hasDerivAt

end ConditionalSpectralAudit
