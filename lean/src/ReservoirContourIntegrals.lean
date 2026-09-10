import ReservoirOuterBounds

/-! Actual circle contribution bounds. Contour deformation is a separate theorem. -/
noncomputable section
open MeasureTheory
open scoped Real Complex BigOperators

namespace ConditionalSpectralExtremes.ReservoirAnalysis

def coefficientContourIntegral (f : Complex → Complex) (N : Nat) (c : Complex) (r : Real) : Complex :=
  (2 * Real.pi * Complex.I : Complex)⁻¹ • ∮ z in C(c, r), f z / z ^ (N + 1)

theorem coefficientContourIntegral_bound (f : Complex → Complex) (N : Nat) (c : Complex)
    (r A B : Real) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hf : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ A)
    (hd : ∀ z ∈ Metric.sphere c r, ‖z ^ (N + 1)‖⁻¹ ≤ B) :
    ‖coefficientContourIntegral f N c r‖ ≤ r * (A * B) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr
  intro z hz
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul (hf z hz) (hd z hz) (inv_nonneg.mpr (norm_nonneg _)) hA

theorem coefficientContourIntegral_outer_bound (f : Complex → Complex) (N : Nat)
    (r A : Real) (hr : 0 < r) (hA : 0 ≤ A)
    (hf : ∀ z ∈ Metric.sphere (0 : Complex) r, ‖f z‖ ≤ A) :
    ‖coefficientContourIntegral f N 0 r‖ ≤ A * (r ^ N)⁻¹ := by
  have hh := coefficientContourIntegral_bound f N 0 r A (r ^ (N + 1))⁻¹ hr.le hA hf (by
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    rw [norm_pow, hz])
  convert! hh using 1
  rw [pow_succ]
  field_simp

theorem indentation_denominator_bound (N : Nat) (hN : 2 ≤ N) (z : Complex)
    (hz : ‖z - 1‖ ≤ (N : Real)⁻¹) : ‖z ^ (N + 1)‖⁻¹ ≤ Real.exp 3 := by
  have hNR : (2 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  have ht : 0 < 1 - (N : Real)⁻¹ := by
    have hi : (N : Real)⁻¹ < 1 := (inv_lt_one₀ hN0).2 (by linarith)
    linarith
  have hzn : 1 - (N : Real)⁻¹ ≤ ‖z‖ := by
    have hh := norm_sub_le (z - 1) z
    have heq : z - 1 - z = (-1 : Complex) := by ring
    rw [heq, norm_neg, norm_one] at hh
    linarith
  have hl := Real.one_sub_inv_le_log_of_pos ht
  have heq : 1 - (1 - (N : Real)⁻¹)⁻¹ = -1 / ((N : Real) - 1) := by
    field_simp [hN0.ne', show (N : Real) - 1 ≠ 0 by linarith, show -1 + (N : Real) ≠ 0 by linarith]
    ring
  rw [heq] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (N + 1))
  have hneg : -(((N + 1 : Nat) : Real) * Real.log (1 - (N : Real)⁻¹)) ≤
      ((N + 1 : Nat) : Real) / ((N : Real) - 1) := by
    simpa only [mul_neg, mul_one_div, neg_div, neg_neg] using neg_le_neg hm
  have hfrac : ((N + 1 : Nat) : Real) / ((N : Real) - 1) ≤ 3 := by
    apply (div_le_iff₀ (by linarith : 0 < (N : Real) - 1)).2
    push_cast
    linarith
  calc
    _ = ‖z‖ ^ (-((N + 1 : Nat) : Real)) := by rw [norm_pow, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    _ ≤ (1 - (N : Real)⁻¹) ^ (-((N + 1 : Nat) : Real)) :=
      Real.rpow_le_rpow_of_nonpos ht hzn (neg_nonpos.mpr (Nat.cast_nonneg (N + 1)))
    _ = Real.exp (-(((N + 1 : Nat) : Real) * Real.log (1 - (N : Real)⁻¹))) := by
      rw [Real.rpow_def_of_pos ht]
      congr 1
      ring
    _ ≤ Real.exp 3 := Real.exp_le_exp.mpr (hneg.trans hfrac)

#print axioms coefficientContourIntegral_bound
#print axioms coefficientContourIntegral_outer_bound
#print axioms indentation_denominator_bound

end ConditionalSpectralExtremes.ReservoirAnalysis
