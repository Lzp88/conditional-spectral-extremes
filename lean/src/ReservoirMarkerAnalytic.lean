import ReservoirPolynomialBridge

/-! Entire marker variable and exact iterated coefficient for the real reservoir weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open Reservoir

theorem reservoirAnalyticCoefficient_differentiable {b N : ℕ} (hb : b ≤ N) :
    Differentiable ℂ (reservoirAnalyticCoefficient b N) := by
  have he : reservoirAnalyticCoefficient b N =
      (fun u => (((reservoirPolynomial N b).coeff N).map Complex.ofRealHom).eval u) :=
    funext (fun u => reservoirAnalyticCoefficient_eq_inner_eval N b N hb le_rfl u)
  rw [he]
  exact Polynomial.differentiable _

theorem reservoir_marker_coefficient {b N : ℕ} (hb : b ≤ N) (l : ℕ) :
    analyticCoefficient (reservoirAnalyticCoefficient b N) l = (reservoirCoefficient N b N l : ℂ) :=
  actual_bivariate_reservoir_coefficient N b N l hb le_rfl

#print axioms reservoirAnalyticCoefficient_differentiable
#print axioms reservoir_marker_coefficient
end ConditionalSpectralExtremes.ReservoirAnalysis
