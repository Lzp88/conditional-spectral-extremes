import ReservoirPolynomialBridge

/-! Actual local estimates for the reservoir contour: no coefficient error is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem norm_harmonicDerivative_near_one (b : Nat) (z : Complex)
    (hz : ‖z - 1‖ ≤ (b : Real)⁻¹) :
    ‖∑ j ∈ Finset.range b, z ^ j‖ ≤ (b : Real) * Real.exp 1 := by
  have hzn : ‖z‖ ≤ 1 + (b : Real)⁻¹ := by
    have hh := norm_add_le (z - 1) (1 : Complex)
    rw [sub_add_cancel, norm_one] at hh
    linarith
  calc
    ‖∑ j ∈ Finset.range b, z ^ j‖ ≤ ∑ j ∈ Finset.range b, ‖z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range b, Real.exp 1 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_pow]
      calc
        ‖z‖ ^ j ≤ (1 + (b : Real)⁻¹) ^ j := by gcongr
        _ ≤ (1 + (b : Real)⁻¹) ^ b :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) (Nat.le_of_lt (Finset.mem_range.mp hj))
        _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
    _ = _ := by simp [nsmul_eq_mul]

theorem harmonicPolynomial_near_one (b : Nat) (z : Complex)
    (hz : ‖z - 1‖ ≤ (b : Real)⁻¹) :
    ‖harmonicPolynomial b z - (harmonicNumber b : Complex)‖ ≤
      ((b : Real) * Real.exp 1) * ‖z - 1‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := harmonicPolynomial b) (f' := fun w => ∑ j ∈ Finset.range b, w ^ j)
    (s := Metric.closedBall (1 : Complex) (b : Real)⁻¹)
    (fun w _ => (hasDerivAt_harmonicPolynomial b w).hasDerivWithinAt)
    (fun w hw => norm_harmonicDerivative_near_one b w (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw))
    (convex_closedBall (1 : Complex) (b : Real)⁻¹)
    (show (1 : Complex) ∈ Metric.closedBall 1 (b : Real)⁻¹ by simp)
    (show z ∈ Metric.closedBall (1 : Complex) (b : Real)⁻¹ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  simpa only [harmonicPolynomial_one] using! hh

theorem norm_exp_sub_one_global (w : Complex) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp w 1

theorem reservoir_correction_near_one (b : Nat) (hb : 0 < b) (z u : Complex) (M : Real)
    (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) (hz : ‖z - 1‖ ≤ (b : Real)⁻¹) :
    ‖Complex.exp (-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))) - 1‖ ≤
      (M * Real.exp 1 * Real.exp (M * Real.exp 1)) * (b : Real) * ‖z - 1‖ := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hbd : (b : Real) * ‖z - 1‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hz hbR.le
    simpa only [mul_inv_cancel₀ hbR.ne'] using hh
  have hnorm : ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ ≤
      (M * Real.exp 1) * ((b : Real) * ‖z - 1‖) := by
    rw [norm_mul, norm_neg]
    calc
      _ ≤ M * (((b : Real) * Real.exp 1) * ‖z - 1‖) :=
        mul_le_mul hu (harmonicPolynomial_near_one b z hz) (norm_nonneg _) hM
      _ = _ := by ring
  have hnormM : ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ ≤ M * Real.exp 1 := by
    exact hnorm.trans (mul_le_of_le_one_right (by positivity) hbd)
  calc
    _ ≤ ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ *
        Real.exp ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ :=
      norm_exp_sub_one_global _
    _ ≤ ((M * Real.exp 1) * ((b : Real) * ‖z - 1‖)) * Real.exp (M * Real.exp 1) := by gcongr
    _ = _ := by ring

def reservoirComparison (b : Nat) (z u : Complex) : Complex :=
  Complex.exp (-u * (harmonicNumber b : Complex)) * Complex.exp (-u * Complex.log (1 - z))

theorem reservoir_difference_factor (b : Nat) (z u : Complex) :
    reservoirKernel b z u - reservoirComparison b z u =
      reservoirComparison b z u *
        (Complex.exp (-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))) - 1) := by
  have hh : reservoirKernel b z u = reservoirComparison b z u *
      Complex.exp (-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))) := by
    unfold reservoirKernel reservoirComparison
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hh]
  ring

theorem norm_reservoir_difference_near_one (b : Nat) (hb : 0 < b) (z u : Complex) (M : Real)
    (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) (hz : ‖z - 1‖ ≤ (b : Real)⁻¹) :
    ‖reservoirKernel b z u - reservoirComparison b z u‖ ≤
      ‖reservoirComparison b z u‖ *
        ((M * Real.exp 1 * Real.exp (M * Real.exp 1)) * (b : Real) * ‖z - 1‖) := by
  rw [reservoir_difference_factor, norm_mul]
  exact mul_le_mul_of_nonneg_left (reservoir_correction_near_one b hb z u M hM hu hz) (norm_nonneg _)

theorem norm_reservoirComparison_eq (b : Nat) (z u : Complex) (hz : 1 - z ≠ 0) :
    ‖reservoirComparison b z u‖ =
      Real.exp (-u.re * harmonicNumber b) * ‖1 - z‖ ^ (-u.re) *
        Real.exp (u.im * Complex.arg (1 - z)) := by
  unfold reservoirComparison
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re, Complex.log_im,
    ← Real.exp_add]
  congr 1
  ring

theorem norm_reservoirComparison_bound (b : Nat) (z u : Complex) (hz : 1 - z ≠ 0)
    (M : Real) (hu : ‖u‖ ≤ M) :
    ‖reservoirComparison b z u‖ ≤
      Real.exp (-u.re * harmonicNumber b) * ‖1 - z‖ ^ (-u.re) * Real.exp (M * Real.pi) := by
  rw [norm_reservoirComparison_eq b z u hz]
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have ha : u.im * Complex.arg (1 - z) ≤ M * Real.pi := by
    calc
      _ ≤ |u.im * Complex.arg (1 - z)| := le_abs_self _
      _ = |u.im| * |Complex.arg (1 - z)| := abs_mul _ _
      _ ≤ _ := mul_le_mul ((Complex.abs_im_le_norm u).trans hu)
        (Complex.abs_arg_le_pi (1 - z)) (abs_nonneg _) hM
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (by positivity)

/-- The local pointwise error used on the indentation and both banks of the slit. -/
theorem reservoir_local_error_bound (b : Nat) (hb : 0 < b) (z u : Complex)
    (hz0 : 1 - z ≠ 0) (M : Real) (hu : ‖u‖ ≤ M) (hz : ‖z - 1‖ ≤ (b : Real)⁻¹) :
    ‖reservoirKernel b z u - reservoirComparison b z u‖ ≤
      (M * Real.exp 1 * Real.exp (M * Real.exp 1) * Real.exp (M * Real.pi)) *
        Real.exp (-u.re * harmonicNumber b) * (b : Real) * ‖z - 1‖ ^ (1 - u.re) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hnorm : 0 < ‖z - 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hz0
    linear_combination -h
  have hpow : ‖z - 1‖ ^ (1 - u.re) = ‖1 - z‖ ^ (-u.re) * ‖z - 1‖ := by
    rw [show 1 - u.re = -u.re + 1 by ring, Real.rpow_add hnorm, Real.rpow_one, norm_sub_rev]
  rw [hpow]
  calc
    _ ≤ ‖reservoirComparison b z u‖ *
      ((M * Real.exp 1 * Real.exp (M * Real.exp 1)) * (b : Real) * ‖z - 1‖) :=
        norm_reservoir_difference_near_one b hb z u M hM hu hz
    _ ≤ (Real.exp (-u.re * harmonicNumber b) * ‖1 - z‖ ^ (-u.re) * Real.exp (M * Real.pi)) *
      ((M * Real.exp 1 * Real.exp (M * Real.exp 1)) * (b : Real) * ‖z - 1‖) := by
        exact mul_le_mul_of_nonneg_right (norm_reservoirComparison_bound b z u hz0 M hu) (by positivity)
    _ = _ := by ring

#print axioms harmonicPolynomial_near_one
#print axioms reservoir_correction_near_one
#print axioms norm_reservoir_difference_near_one
#print axioms reservoir_local_error_bound

end ConditionalSpectralExtremes.ReservoirAnalysis
