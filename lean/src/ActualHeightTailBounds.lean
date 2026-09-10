import ActualMomentUniformBounds
import PairSmoothedHeightTails

/-! Explicit uniform tails for the actual finite and reference smoothed height laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem harmonic_smoothed_coordinate_tail {d : Nat} (s P δ K : Real)
    (hs : 0 < s) (hP : s ≤ P) (hδ : 0 < δ)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (v : Fin d)
    (hH : 0 < harmonicMass m n) (hB : (1/2 : Real) ≤ harmonicTiltNormalizer s t m n) :
    ((coordinateLaw (harmonicTiltSumLaw s t m n q) v) ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ ≤
      2*Real.exp (-(s/2)*K+(s/2)*δ)*momentMajorant P d^q := by
  have hW := harmonic_normalizer_half_weight_positive s t m n hH hB
  let _ := harmonicTiltSumLaw_probability s t m n q hW
  let _ := coordinateLaw_probability (harmonicTiltSumLaw s t m n q) v
  have htail := smoothed_real_box_tail (coordinateLaw (harmonicTiltSumLaw s t m n q) v)
    δ (s/2) K hδ (by positivity)
    (harmonic_coordinate_exp_integrable s (s/2) t m n q v hW)
    (harmonic_coordinate_exp_integrable s (-(s/2)) t m n q v hW)
  have hp := harmonic_single_moment_bound s (s/2) P hs hP (by rw [abs_of_pos (by positivity)]) t m n q v hH hB
  have hm := harmonic_single_moment_bound s (-(s/2)) P hs hP (by rw [abs_neg, abs_of_pos (by positivity)]) t m n q v hH hB
  rw [← coordinateLaw_mgf] at hp hm
  apply htail.trans
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hp hm) (Real.exp_pos (-(s/2)*K+(s/2)*δ)).le]

theorem reference_smoothed_coordinate_tail {d : Nat} (s P δ K : Real)
    (hs : 0 < s) (hP : s ≤ P) (hδ : 0 < δ) (q : Nat) (v : Fin d) :
    ((coordinateLaw (referenceVectorSumLaw s d q) v) ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ ≤
      2*Real.exp (-(s/2)*K+(s/2)*δ)*momentMajorant P d^q := by
  let _ := referenceVectorSumLaw_probability s (by linarith) d q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s d q) v
  have htail := smoothed_real_box_tail (coordinateLaw (referenceVectorSumLaw s d q) v)
    δ (s/2) K hδ (by positivity)
    (reference_coordinate_exp_integrable s (s/2) hs (by linarith) q v)
    (reference_coordinate_exp_integrable s (-(s/2)) hs (by linarith) q v)
  have hp := reference_single_moment_bound s (s/2) P hs hP (by rw [abs_of_pos (by positivity)]) q v
  have hm := reference_single_moment_bound s (-(s/2)) P hs hP (by rw [abs_neg, abs_of_pos (by positivity)]) q v
  rw [← coordinateLaw_mgf] at hp hm
  apply htail.trans
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hp hm) (Real.exp_pos (-(s/2)*K+(s/2)*δ)).le]

theorem harmonic_smoothed_pair_tail (s P δ K : Real) (hs : 0 < s) (hP : s ≤ P) (hδ : 0 < δ)
    (t : Fin 2 → AddCircle (1 : Real)) (m n q : Nat)
    (hH : 0 < harmonicMass m n) (hB : (1/2 : Real) ≤ harmonicTiltNormalizer s t m n) :
    ((pairVectorLaw (harmonicTiltSumLaw s t m n q)) ∗ pairUniformNoise δ).real (pairBox K)ᶜ ≤
      4*Real.exp (-(s/2)*K+(s/2)*δ)*momentMajorant P 2^q := by
  have hW := harmonic_normalizer_half_weight_positive s t m n hH hB
  let _ := harmonicTiltSumLaw_probability s t m n q hW
  let _ := pairVectorLaw_probability (harmonicTiltSumLaw s t m n q)
  have htail := pair_smoothed_box_tail (pairVectorLaw (harmonicTiltSumLaw s t m n q))
    δ (s/2) K hδ (by positivity)
    (fun v => pair_harmonic_coordinate_exp_integrable s (s/2) t m n q v hW)
    (fun v => pair_harmonic_coordinate_exp_integrable s (-(s/2)) t m n q v hW)
  have hp (v : Fin 2) := harmonic_single_moment_bound s (s/2) P hs hP
    (by rw [abs_of_pos (by positivity)]) t m n q v hH hB
  have hm (v : Fin 2) := harmonic_single_moment_bound s (-(s/2)) P hs hP
    (by rw [abs_neg, abs_of_pos (by positivity)]) t m n q v hH hB
  have hsum : (∑ v : Fin 2, (mgf (pairCoordinate v) (pairVectorLaw (harmonicTiltSumLaw s t m n q)) (s/2)+
      mgf (pairCoordinate v) (pairVectorLaw (harmonicTiltSumLaw s t m n q)) (-(s/2)))) ≤ 4*momentMajorant P 2^q := by
    simp_rw [pairVectorLaw_mgf]
    rw [Fin.sum_univ_two]
    linarith [hp 0, hp 1, hm 0, hm 1]
  apply htail.trans
  nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-(s/2)*K+(s/2)*δ)).le]

theorem reference_smoothed_pair_tail (s P δ K : Real) (hs : 0 < s) (hP : s ≤ P) (hδ : 0 < δ) (q : Nat) :
    ((pairVectorLaw (referenceVectorSumLaw s 2 q)) ∗ pairUniformNoise δ).real (pairBox K)ᶜ ≤
      4*Real.exp (-(s/2)*K+(s/2)*δ)*momentMajorant P 2^q := by
  let _ := referenceVectorSumLaw_probability s (by linarith) 2 q
  let _ := pairVectorLaw_probability (referenceVectorSumLaw s 2 q)
  have htail := pair_smoothed_box_tail (pairVectorLaw (referenceVectorSumLaw s 2 q))
    δ (s/2) K hδ (by positivity)
    (fun v => pair_reference_coordinate_exp_integrable s (s/2) hs (by linarith) q v)
    (fun v => pair_reference_coordinate_exp_integrable s (-(s/2)) hs (by linarith) q v)
  have hp (v : Fin 2) := reference_single_moment_bound s (s/2) P hs hP (by rw [abs_of_pos (by positivity)]) q v
  have hm (v : Fin 2) := reference_single_moment_bound s (-(s/2)) P hs hP (by rw [abs_neg, abs_of_pos (by positivity)]) q v
  have hsum : (∑ v : Fin 2, (mgf (pairCoordinate v) (pairVectorLaw (referenceVectorSumLaw s 2 q)) (s/2)+
      mgf (pairCoordinate v) (pairVectorLaw (referenceVectorSumLaw s 2 q)) (-(s/2)))) ≤ 4*momentMajorant P 2^q := by
    simp_rw [pairVectorLaw_mgf]
    rw [Fin.sum_univ_two]
    linarith [hp 0, hp 1, hm 0, hm 1]
  apply htail.trans
  nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-(s/2)*K+(s/2)*δ)).le]

#print axioms harmonic_smoothed_coordinate_tail
#print axioms harmonic_smoothed_pair_tail
#print axioms reference_smoothed_pair_tail
end ConditionalSpectralAudit.FourierHarmonic
