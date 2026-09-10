import SmoothedFrequencyBound
import PairSmoothedFrequencyBound
import VectorCoordinateLaws
import HarmonicMomentBounds

/-! A quantitative bridge from actual harmonic kernel estimates to actual smoothed densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem actual_kernel_normalizer_half {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n)
    (E : Real) (hE : E ≤ 1/2)
    (h0 : ‖harmonicVectorKernel (fun _ => (s : Complex)) t m n-(logSineA s : Complex)^d‖ ≤ E) :
    (1/2 : Real) ≤ harmonicTiltNormalizer s t m n ∧
      0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j := by
  have hA : 1 ≤ logSineA s^d := one_le_pow₀ (logSineA_ge_one s (by linarith))
  obtain ⟨hB,hW⟩ := harmonic_normalizer_positive s hs t m n hH E (by linarith) h0
  exact ⟨by linarith,hW⟩

theorem actual_kernel_frequency_error {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (u : Fin d → Real) (E : Real) (hEn : 0 ≤ E) (hE : E ≤ 1/2)
    (h0 : ‖harmonicVectorKernel (fun _ => (s : Complex)) t m n-(logSineA s : Complex)^d‖ ≤ E)
    (hz : ‖harmonicVectorKernel (fun v => (s : Complex)+u v*Complex.I) t m n-
      ∏ v, complexLogSineA ((s : Complex)+u v*Complex.I)‖ ≤ E) :
    ‖(∫ x, vectorPhase u x ∂harmonicTiltSumLaw s t m n q)-
      (∫ x, vectorPhase u x ∂referenceVectorSumLaw s d q)‖ ≤ 4*q*E := by
  have hA : 1 ≤ logSineA s^d := one_le_pow₀ (logSineA_ge_one s (by linarith))
  exact (actual_tilted_sum_transform_difference s hs t u m n q hH E hEn (by linarith) hz h0).trans
    (div_le_self (by positivity) hA)

theorem actual_kernel_density_comparison_one (s δ T E : Real) (hs : 0 < s)
    (hδ : 0 < δ) (hT : 0 < T) (hEn : 0 ≤ E) (hE : E ≤ 1/2)
    (t : AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hkernel : ∀ u : Real, |u| ≤ T →
      ‖harmonicVectorKernel (fun _ : Fin 1 => (s : Complex)+u*Complex.I) (fun _ => t) m n-
        complexLogSineA ((s : Complex)+u*Complex.I)‖ ≤ E) (x : Real) :
    |smoothedDensity δ (coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0) x-
      smoothedDensity δ (coordinateLaw (referenceVectorSumLaw s 1 q) 0) x| ≤
      (2*Real.pi)⁻¹ * (2*T*(4*q*E)+4*(δ/10)⁻¹^10*T^(-9 : Real)/9) := by
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 1 => (s : Complex)) (fun _ => t) m n-
      (logSineA s : Complex)^1‖ ≤ E := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, complexLogSineA_ofReal, pow_one] using
      hkernel 0 (by simpa using hT.le)
  have hW := (actual_kernel_normalizer_half s hs (fun _ : Fin 1 => t) m n hH E hE h0).2
  let _ := harmonicTiltSumLaw_probability s (fun _ : Fin 1 => t) m n q hW
  let _ := coordinateLaw_probability (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0
  let _ := referenceVectorSumLaw_probability s (by linarith) 1 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  apply smoothedDensity_frequency_bound δ T (4*q*E) hδ hT (by positivity)
  intro u hu
  rw [coordinateLaw_charFun_one, coordinateLaw_charFun_one]
  apply actual_kernel_frequency_error s hs (fun _ : Fin 1 => t) m n q hH (fun _ => u) E hEn hE h0
  simpa only [Fin.prod_univ_one] using hkernel u (abs_le.mpr hu)

theorem actual_kernel_density_comparison_two (s δ T E : Real) (hs : 0 < s)
    (hδ : 0 < δ) (hT : 0 < T) (hEn : 0 ≤ E) (hE : E ≤ 1/2)
    (t : Fin 2 → AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hkernel : ∀ u : Fin 2 → Real, (∀ v, |u v| ≤ T) →
      ‖harmonicVectorKernel (fun v => (s : Complex)+u v*Complex.I) t m n-
        ∏ v, complexLogSineA ((s : Complex)+u v*Complex.I)‖ ≤ E) (x : PairSpace) :
    |pairSmoothedDensity δ (pairVectorLaw (harmonicTiltSumLaw s t m n q)) x-
      pairSmoothedDensity δ (pairVectorLaw (referenceVectorSumLaw s 2 q)) x| ≤
      ((2*Real.pi)^2)⁻¹ *
        (4*T^2*(4*q*E)+4*(2*(δ/10)⁻¹^10*T^(-9 : Real)/9)*((200/9 : Real)/δ)) := by
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 2 => (s : Complex)) t m n-
      (logSineA s : Complex)^2‖ ≤ E := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, complexLogSineA_ofReal,
      Fin.prod_univ_two, pow_two] using hkernel (fun _ => 0) (fun _ => by simpa using hT.le)
  have hW := (actual_kernel_normalizer_half s hs t m n hH E hE h0).2
  let _ := harmonicTiltSumLaw_probability s t m n q hW
  let _ := pairVectorLaw_probability (harmonicTiltSumLaw s t m n q)
  let _ := referenceVectorSumLaw_probability s (by linarith) 2 q
  let _ := pairVectorLaw_probability (referenceVectorSumLaw s 2 q)
  apply pairSmoothedDensity_frequency_bound δ T (4*q*E) hδ hT (by positivity)
  intro u hu
  rw [pairVectorLaw_charFun, pairVectorLaw_charFun]
  apply actual_kernel_frequency_error s hs t m n q hH ![(ofLp u).1,(ofLp u).2] E hEn hE h0
  apply hkernel
  intro v
  fin_cases v
  · exact abs_le.mpr (mem_pairBox T u |>.mp hu).1
  · exact abs_le.mpr (mem_pairBox T u |>.mp hu).2

#print axioms actual_kernel_density_comparison_one
#print axioms actual_kernel_density_comparison_two
end ConditionalSpectralAudit.FourierHarmonic
