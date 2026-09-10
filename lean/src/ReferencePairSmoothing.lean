import ReferenceCoordinateIndependence
import PairUniformNoise
import FinePathComparison

/-! Exact reference independence after adding the actual two-point noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set WithLp
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem reference_pair_smoothed_independent (s δ : Real) (hs : -1 < s) (hδ : 0 < δ) (q : Nat) :
    (pairVectorLaw (referenceVectorSumLaw s 2 q)) ∗ pairUniformNoise δ =
      (((coordinateLaw (referenceVectorSumLaw s 1 q) 0) ∗ tenUniformNoise δ).prod
        ((coordinateLaw (referenceVectorSumLaw s 1 q) 0) ∗ tenUniformNoise δ)).map (toLp 2) := by
  let _ := referenceVectorSumLaw_probability s hs 1 q
  let _ := referenceVectorSumLaw_probability s hs 2 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  let _ := pairVectorLaw_probability (referenceVectorSumLaw s 2 q)
  let _ := tenUniformNoise_probability δ hδ
  let _ := pairUniformNoise_probability δ hδ
  apply Measure.ext_of_charFun
  ext u
  rw [charFun_conv, reference_pair_law_eq_independent s hs q, charFun_prod,
    pairUniformNoise_charFun δ hδ, charFun_prod]
  simp only [charFun_conv]
  ring

#print axioms reference_pair_smoothed_independent
end ConditionalSpectralAudit.FourierHarmonic
