import FiniteTiltedMoments
import LambdaAnalysis

/-! Crude actual shifted-kernel bounds sufficient for every polynomial spatial-tail target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem norm_chord_le_two (t : AddCircle (1 : Real)) : ‖(1 : Complex)-fourier 1 t‖ ≤ 2 := by
  calc
    _ ≤ ‖(1 : Complex)‖+‖fourier 1 t‖ := norm_sub_le _ _
    _ = 2 := by simp; norm_num

theorem logSineA_ge_one (s : Real) (hs : -1 < s) : 1 ≤ logSineA s := by
  rw [logSineA_eq_exp_lambda s hs]
  exact Real.one_le_exp_iff.mpr (lambda_nonneg hs)

theorem logSineA_le_two_rpow (s : Real) (hs : 0 ≤ s) : logSineA s ≤ (2 : Real)^s := by
  have hi := FourierGeneral.actual_mellin_integrable s (by linarith)
  have he := FourierGeneral.actual_mellin_integral s (by linarith)
  change (∫ t : AddCircle (1 : Real), ‖(1 : Complex)-fourier 1 t‖ ^ s
    ∂AddCircle.haarAddCircle) = logSineA s at he
  rw [← he]
  calc
    _ ≤ ∫ _ : AddCircle (1 : Real), (2 : Real)^s ∂AddCircle.haarAddCircle := by
      apply integral_mono hi (integrable_const _)
      intro t
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_chord_le_two t) hs
    _ = _ := by simp

theorem realHarmonicVectorKernel_nonneg {d : Nat} (s : Fin d → Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) :
    0 ≤ realHarmonicVectorKernel s t m n := by
  unfold realHarmonicVectorKernel
  exact div_nonneg (Finset.sum_nonneg (fun j _ => by positivity)) (harmonicMass_nonneg m n)

theorem realHarmonicVectorKernel_bound {d : Nat} (s : Fin d → Real) (hs : ∀ v, 0 ≤ s v)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n) :
    realHarmonicVectorKernel s t m n ≤ ∏ v, (2 : Real)^s v := by
  unfold realHarmonicVectorKernel
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ ∑ j ∈ Finset.Ico m n, (j : Real)⁻¹ * ∏ v, (2 : Real)^s v := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod
      · intro v hv; positivity
      · intro v hv
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_chord_le_two _) (hs v)
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold harmonicMass
      ring

theorem realHarmonicVectorKernel_uniform_bound {d : Nat} (s : Fin d → Real)
    (P : Real) (hs : ∀ v, 0 ≤ s v) (hP : ∀ v, s v ≤ P)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n) :
    realHarmonicVectorKernel s t m n ≤ ((2 : Real)^P)^d := by
  apply (realHarmonicVectorKernel_bound s hs t m n hH).trans
  calc
    _ ≤ ∏ _ : Fin d, (2 : Real)^P := by
      apply Finset.prod_le_prod
      · intro v hv; positivity
      · intro v hv
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hP v)
    _ = _ := by simp

#print axioms realHarmonicVectorKernel_uniform_bound
#print axioms logSineA_ge_one
end ConditionalSpectralAudit.FourierHarmonic
