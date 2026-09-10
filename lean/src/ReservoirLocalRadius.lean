import ReservoirContourBounds

/-! The true local bound on every fixed multiple of the scale `1/b`. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem norm_harmonicDerivative_fixed_radius (b : Nat) (z : Complex) (K : Real)
    (hK : 0 ≤ K) (hz : ‖z - 1‖ ≤ K / b) :
    ‖∑ j ∈ Finset.range b, z ^ j‖ ≤ (b : Real) * Real.exp K := by
  have hzn : ‖z‖ ≤ 1 + K / b := by
    have hh := norm_add_le (z - 1) (1 : Complex)
    rw [sub_add_cancel, norm_one] at hh
    linarith
  have hp : (1 + K / b) ^ b ≤ Real.exp K := by
    simpa only [neg_div, sub_neg_eq_add, neg_neg] using
      (Real.one_sub_div_pow_le_exp_neg (n := b) (t := -K) (by linarith [Nat.cast_nonneg (α := Real) b]))
  calc
    _ ≤ ∑ j ∈ Finset.range b, ‖z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range b, Real.exp K := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg z) hzn j).trans
        ((pow_le_pow_right₀ (le_add_of_nonneg_right (div_nonneg hK (Nat.cast_nonneg b)))
          (Nat.le_of_lt (Finset.mem_range.mp hj))).trans hp)
    _ = _ := by simp [nsmul_eq_mul]

theorem harmonicPolynomial_fixed_radius (b : Nat) (z : Complex) (K : Real)
    (hK : 0 ≤ K) (hz : ‖z - 1‖ ≤ K / b) :
    ‖harmonicPolynomial b z - (harmonicNumber b : Complex)‖ ≤
      ((b : Real) * Real.exp K) * ‖z - 1‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := harmonicPolynomial b) (f' := fun w => ∑ j ∈ Finset.range b, w ^ j)
    (s := Metric.closedBall (1 : Complex) (K / b))
    (fun w _ => (hasDerivAt_harmonicPolynomial b w).hasDerivWithinAt)
    (fun w hw => norm_harmonicDerivative_fixed_radius b w K hK
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw))
    (convex_closedBall (1 : Complex) (K / b))
    (show (1 : Complex) ∈ Metric.closedBall 1 (K / b) by simp [div_nonneg hK (Nat.cast_nonneg b)])
    (show z ∈ Metric.closedBall (1 : Complex) (K / b) by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  simpa only [harmonicPolynomial_one] using! hh

theorem reservoir_correction_fixed_radius (b : Nat) (hb : 0 < b) (z u : Complex)
    (M K : Real) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : ‖u‖ ≤ M) (hz : ‖z - 1‖ ≤ K / b) :
    ‖Complex.exp (-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))) - 1‖ ≤
      (M * Real.exp K * Real.exp (M * K * Real.exp K)) * (b : Real) * ‖z - 1‖ := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hbd : (b : Real) * ‖z - 1‖ ≤ K := by
    have hh := mul_le_mul_of_nonneg_left hz hbR.le
    simpa only [mul_div_cancel₀ _ hbR.ne'] using hh
  have hnorm : ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ ≤
      (M * Real.exp K) * ((b : Real) * ‖z - 1‖) := by
    rw [norm_mul, norm_neg]
    calc
      _ ≤ M * (((b : Real) * Real.exp K) * ‖z - 1‖) :=
        mul_le_mul hu (harmonicPolynomial_fixed_radius b z K hK hz) (norm_nonneg _) hM
      _ = _ := by ring
  have hnormM : ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ ≤ M * K * Real.exp K := by
    calc
      _ ≤ (M * Real.exp K) * ((b : Real) * ‖z - 1‖) := hnorm
      _ ≤ (M * Real.exp K) * K := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ *
        Real.exp ‖-u * (harmonicPolynomial b z - (harmonicNumber b : Complex))‖ :=
      norm_exp_sub_one_global _
    _ ≤ ((M * Real.exp K) * ((b : Real) * ‖z - 1‖)) * Real.exp (M * K * Real.exp K) := by gcongr
    _ = _ := by ring

theorem reservoir_local_error_fixed_radius (b : Nat) (hb : 0 < b) (z u : Complex)
    (hz0 : 1 - z ≠ 0) (M K : Real) (hu : ‖u‖ ≤ M) (hK : 0 ≤ K) (hz : ‖z - 1‖ ≤ K / b) :
    ‖reservoirKernel b z u - reservoirComparison b z u‖ ≤
      (M * Real.exp K * Real.exp (M * K * Real.exp K) * Real.exp (M * Real.pi)) *
        Real.exp (-u.re * harmonicNumber b) * (b : Real) * ‖z - 1‖ ^ (1 - u.re) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hnorm : 0 < ‖z - 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hz0
    linear_combination -h
  have hpow : ‖z - 1‖ ^ (1 - u.re) = ‖1 - z‖ ^ (-u.re) * ‖z - 1‖ := by
    rw [show 1 - u.re = -u.re + 1 by ring, Real.rpow_add hnorm, Real.rpow_one, norm_sub_rev]
  rw [hpow, reservoir_difference_factor, norm_mul]
  calc
    _ ≤ (Real.exp (-u.re * harmonicNumber b) * ‖1 - z‖ ^ (-u.re) * Real.exp (M * Real.pi)) *
      ((M * Real.exp K * Real.exp (M * K * Real.exp K)) * (b : Real) * ‖z - 1‖) :=
        mul_le_mul (norm_reservoirComparison_bound b z u hz0 M hu)
          (reservoir_correction_fixed_radius b hb z u M K hM hK hu hz) (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms reservoir_local_error_fixed_radius
end ConditionalSpectralExtremes.ReservoirAnalysis
