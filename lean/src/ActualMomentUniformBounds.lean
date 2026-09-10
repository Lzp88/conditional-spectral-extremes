import ActualCoordinateMoments
import HarmonicMomentBounds

/-! Uniform real coordinate moments of both actual laws, with all shifts in [-s/2,s/2]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def momentMajorant (P : Real) (d : Nat) : Real := 2*((2 : Real)^(3*P/2))^d

theorem momentMajorant_pos (P : Real) (d : Nat) : 0 < momentMajorant P d := by
  unfold momentMajorant; positivity

theorem single_shift_range {d : Nat} (s r P : Real) (hs : 0 < s) (hP : s ≤ P)
    (hr : |r| ≤ s/2) (v i : Fin d) :
    0 < s+(Pi.single v r : Fin d → Real) i ∧ s+(Pi.single v r : Fin d → Real) i ≤ 3*P/2 := by
  have hrange := abs_le.mp hr
  by_cases h : i=v
  · subst i
    simp only [Pi.single_eq_same]
    constructor <;> linarith
  · simp only [Pi.single_eq_of_ne h, add_zero]
    exact ⟨hs, by linarith⟩

theorem harmonic_normalizer_half_weight_positive {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n)
    (hB : (1/2 : Real) ≤ harmonicTiltNormalizer s t m n) :
    0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j := by
  exact (div_pos_iff_of_pos_right hH).mp (by linarith : 0 < harmonicTiltNormalizer s t m n)

theorem harmonic_single_moment_bound {d : Nat} (s r P : Real) (hs : 0 < s) (hP : s ≤ P)
    (hr : |r| ≤ s/2) (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (v : Fin d)
    (hH : 0 < harmonicMass m n) (hB : (1/2 : Real) ≤ harmonicTiltNormalizer s t m n) :
    (∫ x, Real.exp (r*x v) ∂harmonicTiltSumLaw s t m n q) ≤ momentMajorant P d ^ q := by
  have hW := harmonic_normalizer_half_weight_positive s t m n hH hB
  have hpos := fun i => (single_shift_range s r P hs hP hr v i).1
  have hb := realHarmonicVectorKernel_uniform_bound (fun i => s+(Pi.single v r : Fin d → Real) i)
    (3*P/2) (fun i => (hpos i).le) (fun i => (single_shift_range s r P hs hP hr v i).2) t m n hH
  have he := harmonicTiltSumLaw_moment s hs (Pi.single v r) hpos t m n q hH hW
  rw [vectorExp_single_fun] at he
  rw [he]
  apply pow_le_pow_left₀ (div_nonneg (realHarmonicVectorKernel_nonneg _ _ _ _) (by linarith))
  apply (div_le_iff₀ (by linarith : 0 < harmonicTiltNormalizer s t m n)).mpr
  unfold momentMajorant
  nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ ((2 : Real)^(3*P/2))^d)]

theorem reference_single_moment_bound {d : Nat} (s r P : Real) (hs : 0 < s) (hP : s ≤ P)
    (hr : |r| ≤ s/2) (q : Nat) (v : Fin d) :
    (∫ x, Real.exp (r*x v) ∂referenceVectorSumLaw s d q) ≤ momentMajorant P d ^ q := by
  have hpos := fun i => (single_shift_range s r P hs hP hr v i).1
  have he := referenceVectorSumLaw_moment s (by linarith) d q (Pi.single v r)
    (fun i => by linarith [hpos i])
  rw [vectorExp_single_fun] at he
  rw [he]
  have hA : 1 ≤ logSineA s^d := one_le_pow₀ (logSineA_ge_one s (by linarith))
  have hn : 0 ≤ ∏ i, logSineA (s+(Pi.single v r : Fin d → Real) i) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (logSineA_pos _ (by linarith [hpos i])).le
  apply pow_le_pow_left₀ (div_nonneg hn (by linarith))
  apply (div_le_self hn hA).trans
  have hb : (∏ i, logSineA (s+(Pi.single v r : Fin d → Real) i)) ≤ ((2 : Real)^(3*P/2))^d := by
    calc
      _ ≤ ∏ _ : Fin d, (2 : Real)^(3*P/2) := by
        apply Finset.prod_le_prod
        · intro i hi; exact (logSineA_pos _ (by linarith [hpos i])).le
        · intro i hi
          exact (logSineA_le_two_rpow _ (hpos i).le).trans
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (single_shift_range s r P hs hP hr v i).2)
      _ = _ := by simp
  unfold momentMajorant
  linarith [show 0 ≤ ((2 : Real)^(3*P/2))^d by positivity]

#print axioms harmonic_single_moment_bound
#print axioms reference_single_moment_bound
end ConditionalSpectralAudit.FourierHarmonic
