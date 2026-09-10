import ActualKernelTotalVariation
import ActualHeightTailBounds
import SmoothingTotalVariation
import PairSmoothingTotalVariation

/-! Full one- and two-point L1 density comparison from actual harmonic kernels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem actual_kernel_l1_one (s P δ T K E : Real) (hs : 0 < s) (hP : s ≤ P)
    (hδ : 0 < δ) (hT : 0 < T) (hK : 0 ≤ K) (hEn : 0 ≤ E) (hE : E ≤ 1/2)
    (t : AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hkernel : ∀ u : Real, |u| ≤ T →
      ‖harmonicVectorKernel (fun _ : Fin 1 => (s : Complex)+u*Complex.I) (fun _ => t) m n-
        complexLogSineA ((s : Complex)+u*Complex.I)‖ ≤ E) :
    (∫ x : Real, |smoothedDensity δ
      (coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0) x -
      smoothedDensity δ (coordinateLaw (referenceVectorSumLaw s 1 q) 0) x|) ≤
      smoothingErrorOne P s δ T K E q := by
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 1 => (s : Complex)) (fun _ => t) m n-
      (logSineA s : Complex)^1‖ ≤ E := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, complexLogSineA_ofReal, pow_one] using
      hkernel 0 (by simpa using hT.le)
  obtain ⟨hB,hW⟩ := actual_kernel_normalizer_half s hs (fun _ : Fin 1 => t) m n hH E hE h0
  let _ := harmonicTiltSumLaw_probability s (fun _ : Fin 1 => t) m n q hW
  let _ := coordinateLaw_probability (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0
  let _ := referenceVectorSumLaw_probability s (by linarith) 1 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  have hd := actual_kernel_density_comparison_one s δ T E hs hδ hT hEn hE t m n q hH hkernel
  have ht := smoothedDensity_l1_box_bound δ K _ hδ hK
    (coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0)
    (coordinateLaw (referenceVectorSumLaw s 1 q) 0) hd
  have hfinite := harmonic_smoothed_coordinate_tail s P δ K hs hP hδ (fun _ : Fin 1 => t) m n q 0 hH hB
  have href := reference_smoothed_coordinate_tail s P δ K hs hP hδ q (0 : Fin 1)
  unfold smoothingErrorOne
  linarith

theorem actual_kernel_l1_two (s P δ T K E : Real) (hs : 0 < s) (hP : s ≤ P)
    (hδ : 0 < δ) (hT : 0 < T) (hK : 0 ≤ K) (hEn : 0 ≤ E) (hE : E ≤ 1/2)
    (t : Fin 2 → AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hkernel : ∀ u : Fin 2 → Real, (∀ v, |u v| ≤ T) →
      ‖harmonicVectorKernel (fun v => (s : Complex)+u v*Complex.I) t m n-
        ∏ v, complexLogSineA ((s : Complex)+u v*Complex.I)‖ ≤ E) :
    (∫ x : PairSpace, |pairSmoothedDensity δ
      (pairVectorLaw (harmonicTiltSumLaw s t m n q)) x -
      pairSmoothedDensity δ (pairVectorLaw (referenceVectorSumLaw s 2 q)) x|) ≤
      smoothingErrorTwo P s δ T K E q := by
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 2 => (s : Complex)) t m n-
      (logSineA s : Complex)^2‖ ≤ E := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, complexLogSineA_ofReal,
      Fin.prod_univ_two, pow_two] using hkernel (fun _ => 0) (fun _ => by simpa using hT.le)
  obtain ⟨hB,hW⟩ := actual_kernel_normalizer_half s hs t m n hH E hE h0
  let _ := harmonicTiltSumLaw_probability s t m n q hW
  let _ := pairVectorLaw_probability (harmonicTiltSumLaw s t m n q)
  let _ := referenceVectorSumLaw_probability s (by linarith) 2 q
  let _ := pairVectorLaw_probability (referenceVectorSumLaw s 2 q)
  have hd := actual_kernel_density_comparison_two s δ T E hs hδ hT hEn hE t m n q hH hkernel
  have ht := pairSmoothedDensity_l1_box_bound δ K _ hδ hK
    (pairVectorLaw (harmonicTiltSumLaw s t m n q)) (pairVectorLaw (referenceVectorSumLaw s 2 q)) hd
  have hfinite := harmonic_smoothed_pair_tail s P δ K hs hP hδ t m n q hH hB
  have href := reference_smoothed_pair_tail s P δ K hs hP hδ q
  unfold smoothingErrorTwo
  linarith

#print axioms actual_kernel_l1_one
#print axioms actual_kernel_l1_two
end ConditionalSpectralAudit.FourierHarmonic

