import ReservoirBankBounds

noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem logContourIntegrand_add_two_pi_I (b N : Nat) (u w : Complex) :
    logContourIntegrand b N u (w + 2 * Real.pi * Complex.I) = logContourIntegrand b N u w := by
  have he : Complex.exp (w + 2 * Real.pi * Complex.I) = Complex.exp w := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold logContourIntegrand
  rw [he, mul_add, Complex.exp_add, exp_neg_nat_mul N (2 * Real.pi * Complex.I)]
  simp [Complex.exp_two_pi_mul_I]

theorem logContourIntegrand_top_bank (b N : Nat) (u : Complex) (x delta : Real) :
    logContourIntegrand b N u (x + (2 * Real.pi - delta) * Complex.I) =
      logContourIntegrand b N u (x + (-delta : Real) * Complex.I) := by
  have he : ((x : Complex) + (2 * Real.pi - delta) * Complex.I) =
      ((x : Complex) + (-delta : Real) * Complex.I) + 2 * Real.pi * Complex.I := by push_cast; ring
  rw [he, logContourIntegrand_add_two_pi_I]

theorem logContourIntegrand_sub_two_pi (b N : Nat) (u : Complex) (x y : Real) :
    logContourIntegrand b N u (x + y * Complex.I) =
      logContourIntegrand b N u (x + (y - 2 * Real.pi) * Complex.I) := by
  have he : ((x : Complex) + y * Complex.I) =
      ((x : Complex) + (y - 2 * Real.pi) * Complex.I) + 2 * Real.pi * Complex.I := by ring
  rw [he, logContourIntegrand_add_two_pi_I]

theorem one_sub_exp_mem_slitPlane_of_sin_ne_zero (x y : Real) (hy : Real.sin y ≠ 0) :
    1 - Complex.exp ((x : Complex) + y * Complex.I) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  simpa [Complex.exp_im] using neg_ne_zero.mpr (mul_ne_zero (Real.exp_ne_zero x) hy)

theorem logContourIntegrand_continuous_bank (b N : Nat) (u : Complex) (y : Real)
    (hy : Real.sin y ≠ 0) :
    Continuous (fun x : Real => logContourIntegrand b N u (x + y * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hs := one_sub_exp_mem_slitPlane_of_sin_ne_zero x y hy
  have hf := ((reservoirKernel_analyticAt b (Complex.exp ((x : Complex) + y * Complex.I)) u hs).sub
    (reservoirComparison_analyticAt b (Complex.exp ((x : Complex) + y * Complex.I)) u hs)).continuousAt
  have hp : ContinuousAt (fun t : Real => Complex.exp ((t : Complex) + y * Complex.I)) x := by fun_prop
  have hc : ContinuousAt (fun t : Real =>
      reservoirKernel b (Complex.exp ((t : Complex) + y * Complex.I)) u -
      reservoirComparison b (Complex.exp ((t : Complex) + y * Complex.I)) u) x :=
    hf.comp (f := fun t : Real => Complex.exp ((t : Complex) + y * Complex.I)) hp
  have he : ContinuousAt (fun t : Real => Complex.exp (-(N : Complex) * ((t : Complex) + y * Complex.I))) x := by fun_prop
  exact hc.mul he

theorem sin_ne_zero_of_abs_eq_small (y delta : Real) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hy : |y| = delta) : Real.sin y ≠ 0 := by
  have hp : delta < Real.pi := by linarith [Real.pi_gt_three]
  rcases (abs_eq (le_of_lt hd)).mp hy with h | h
  · rw [h]
    exact (Real.sin_pos_of_pos_of_lt_pi hd hp).ne'
  · rw [h, Real.sin_neg]
    exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hd hp).ne'

#print axioms logContourIntegrand_add_two_pi_I
#print axioms logContourIntegrand_continuous_bank
end ConditionalSpectralExtremes.ReservoirAnalysis
