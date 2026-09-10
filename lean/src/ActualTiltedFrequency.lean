import ReferenceVectorTilt
import NormalizedKernelPower

/-! The genuine finite and continuous tilted probability laws, with the full q-power error. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def harmonicTiltNormalizer {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (m n : Nat) : Real := (∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) / harmonicMass m n

theorem harmonicVectorKernel_real_cast {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) :
    harmonicVectorKernel (fun _ => (s : Complex)) t m n = (harmonicTiltNormalizer s t m n : Complex) := by
  rw [harmonicVectorKernel_real]
  simp only [harmonicTiltNormalizer, Complex.ofReal_div]

theorem harmonicTiltSumLaw_probability {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    IsProbabilityMeasure (harmonicTiltSumLaw s t m n q) := by
  let _ := harmonicTiltLaw_probability s t m n hW
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  unfold harmonicTiltSumLaw
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

theorem harmonic_normalizer_positive {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n)
    (E : Real) (hE : E ≤ logSineA s ^ d / 2)
    (h0 : ‖harmonicVectorKernel (fun _ => (s : Complex)) t m n - (logSineA s : Complex) ^ d‖ ≤ E) :
    logSineA s ^ d / 2 ≤ harmonicTiltNormalizer s t m n ∧
      0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j := by
  have ha : 0 < logSineA s ^ d := pow_pos (logSineA_pos s (by linarith)) _
  rw [harmonicVectorKernel_real_cast, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h0
  have hb : logSineA s ^ d / 2 ≤ harmonicTiltNormalizer s t m n := by
    have hh := (abs_le.mp h0).1
    linarith
  refine ⟨hb, ?_⟩
  have hbp : 0 < harmonicTiltNormalizer s t m n := lt_of_lt_of_le (by positivity) hb
  exact (div_pos_iff_of_pos_right hH).mp hbp

theorem actual_tilted_sum_transform_difference {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (u : Fin d → Real) (m n q : Nat)
    (hH : 0 < harmonicMass m n) (E : Real) (hE : 0 ≤ E) (hEs : E ≤ logSineA s ^ d / 2)
    (hB : ‖harmonicVectorKernel (fun v => (s : Complex) + u v * Complex.I) t m n -
      ∏ v, complexLogSineA ((s : Complex) + u v * Complex.I)‖ ≤ E)
    (h0 : ‖harmonicVectorKernel (fun _ => (s : Complex)) t m n - (logSineA s : Complex) ^ d‖ ≤ E) :
    ‖(∫ x, vectorPhase u x ∂harmonicTiltSumLaw s t m n q) -
      (∫ x, vectorPhase u x ∂referenceVectorSumLaw s d q)‖ ≤ 4*q*E/(logSineA s ^ d) := by
  obtain ⟨hba, hW⟩ := harmonic_normalizer_positive s hs t m n hH E hEs h0
  have ha : 0 < logSineA s ^ d := pow_pos (logSineA_pos s (by linarith)) _
  have hb : 0 < harmonicTiltNormalizer s t m n := lt_of_lt_of_le (by positivity) hba
  have hz : ‖harmonicVectorKernel (fun v => (s : Complex) + u v * Complex.I) t m n /
      (harmonicTiltNormalizer s t m n : Complex)‖ ≤ 1 := by
    rw [← harmonicVectorKernel_real_cast, ← harmonicTiltLaw_transform s hs t u m n hH]
    exact harmonicTiltLaw_transform_norm_le_one s t u m n hW
  have hbaE : |harmonicTiltNormalizer s t m n - logSineA s ^ d| ≤ E := by
    simpa only [harmonicVectorKernel_real_cast, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using h0
  have hh := normalized_kernel_power_difference
    (harmonicVectorKernel (fun v => (s : Complex) + u v * Complex.I) t m n)
    (∏ v, complexLogSineA ((s : Complex) + u v * Complex.I))
    (harmonicTiltNormalizer s t m n) (logSineA s ^ d) E hb ha hz
    (reference_Gamma_product_norm s (by linarith) d u) hB hbaE q
  rw [harmonicTiltSumLaw_transform s hs t u m n q hH hW,
    referenceVectorSumLaw_transform s (by linarith) d q u, harmonicVectorKernel_real_cast]
  have hcast : ((logSineA s ^ d : Real) : Complex) = (logSineA s : Complex) ^ d := by push_cast; rfl
  rw [hcast] at hh
  apply hh.trans
  apply (div_le_div_iff₀ hb ha).mpr
  have hqe : 0 ≤ (q : Real)*E := mul_nonneg (Nat.cast_nonneg q) hE
  nlinarith [mul_nonneg hqe (sub_nonneg.mpr hba)]

#print axioms actual_tilted_sum_transform_difference
end ConditionalSpectralAudit.FourierHarmonic
