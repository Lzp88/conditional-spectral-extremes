import ReservoirContourBounds

/-! Polynomial bounds on the actual outer circle, sufficient for the reservoir error term. -/
noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem harmonicNumber_eq_harmonic (b : Nat) : harmonicNumber b = (harmonic b : Real) := by
  simp only [harmonicNumber, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem harmonicNumber_nonneg (b : Nat) : 0 ≤ harmonicNumber b := by
  unfold harmonicNumber
  positivity

theorem harmonicNumber_log_bound (b : Nat) : harmonicNumber b ≤ 1 + Real.log (b : Real) := by
  rw [harmonicNumber_eq_harmonic]
  exact harmonic_le_one_add_log b

theorem harmonicPolynomial_outer_bound (b : Nat) (z : Complex)
    (hz : ‖z‖ ≤ 1 + (b : Real)⁻¹) :
    ‖harmonicPolynomial b z‖ ≤ Real.exp 1 * harmonicNumber b := by
  unfold harmonicPolynomial harmonicNumber
  calc
    _ ≤ ∑ j ∈ Finset.range b, ‖z ^ (j + 1) / ((j + 1 : Nat) : Complex)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range b, Real.exp 1 / ((j + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_div, norm_pow, Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc
        ‖z‖ ^ (j + 1) ≤ (1 + (b : Real)⁻¹) ^ (j + 1) := by gcongr
        _ ≤ (1 + (b : Real)⁻¹) ^ b :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) (by have h := Finset.mem_range.mp hj; omega)
        _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring

theorem outer_distance_bounds (b : Nat) (hb : 0 < b) (z : Complex)
    (hz : ‖z‖ = 1 + (b : Real)⁻¹) : (b : Real)⁻¹ ≤ ‖1 - z‖ ∧ ‖1 - z‖ ≤ 3 := by
  have hb1 : (1 : Real) ≤ b := by exact_mod_cast hb
  have hi : (b : Real)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity : (0 : Real) < b)).2 hb1
  have hlo := norm_sub_norm_le z (1 : Complex)
  have hhi := norm_sub_le (1 : Complex) z
  rw [hz, norm_one, norm_sub_rev] at hlo
  rw [hz, norm_one] at hhi
  constructor <;> linarith

theorem norm_log_outer_bound (b : Nat) (hb : 0 < b) (z : Complex)
    (hz : ‖z‖ = 1 + (b : Real)⁻¹) :
    ‖Complex.log (1 - z)‖ ≤ Real.log (b : Real) + Real.log 3 + Real.pi := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hb1 : (1 : Real) ≤ b := by exact_mod_cast hb
  obtain ⟨hlo, hhi⟩ := outer_distance_bounds b hb z hz
  have hpos : 0 < ‖1 - z‖ := (inv_pos.mpr hbR).trans_le hlo
  have hl := Real.log_le_log (inv_pos.mpr hbR) hlo
  rw [Real.log_inv] at hl
  have hh := Real.log_le_log hpos hhi
  have hlogb := Real.log_nonneg hb1
  have hlog3 : 0 ≤ Real.log (3 : Real) := Real.log_nonneg (by norm_num)
  have habs : |Real.log ‖1 - z‖| ≤ Real.log (b : Real) + Real.log 3 := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    ‖Complex.log (1 - z)‖ ≤ |(Complex.log (1 - z)).re| + |(Complex.log (1 - z)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add habs (Complex.abs_arg_le_pi _)

theorem reservoirKernel_outer_polynomial_bound (b : Nat) (hb : 0 < b) (z u : Complex)
    (hz : ‖z‖ = 1 + (b : Real)⁻¹) (M : Real) (hu : ‖u‖ ≤ M) :
    ‖reservoirKernel b z u‖ ≤
      Real.exp (M * (Real.exp 1 + Real.log 3 + Real.pi)) *
        (b : Real) ^ (M * (Real.exp 1 + 1)) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hHb := (harmonicPolynomial_outer_bound b z hz.le).trans
    (mul_le_mul_of_nonneg_left (harmonicNumber_log_bound b) (Real.exp_pos 1).le)
  have hlog := norm_log_outer_bound b hb z hz
  have hn : ‖-u * (Complex.log (1 - z) + harmonicPolynomial b z)‖ ≤
      M * ((Real.exp 1 + 1) * Real.log (b : Real) + (Real.exp 1 + Real.log 3 + Real.pi)) := by
    rw [norm_mul, norm_neg]
    have hsum := (norm_add_le (Complex.log (1 - z)) (harmonicPolynomial b z)).trans (add_le_add hlog hHb)
    have hh := mul_le_mul hu hsum (norm_nonneg _) hM
    convert! hh using 1
    ring
  calc
    _ ≤ Real.exp ‖-u * (Complex.log (1 - z) + harmonicPolynomial b z)‖ := Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (M * ((Real.exp 1 + 1) * Real.log (b : Real) + (Real.exp 1 + Real.log 3 + Real.pi))) :=
      Real.exp_le_exp.mpr hn
    _ = _ := by
      rw [Real.rpow_def_of_pos hbR, ← Real.exp_add]
      congr 1
      ring

theorem reservoirComparison_outer_polynomial_bound (b : Nat) (hb : 0 < b) (z u : Complex)
    (hz : ‖z‖ = 1 + (b : Real)⁻¹) (M : Real) (hu : ‖u‖ ≤ M) :
    ‖reservoirComparison b z u‖ ≤
      Real.exp (M * (1 + Real.log 3 + Real.pi)) * (b : Real) ^ (2 * M) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hfirst : ‖Complex.exp (-u * (harmonicNumber b : Complex))‖ ≤
      Real.exp (M * (1 + Real.log (b : Real))) := by
    calc
      _ ≤ Real.exp (‖u‖ * harmonicNumber b) := by
        simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (harmonicNumber_nonneg b)] using Complex.norm_exp_le_exp_norm (-u * (harmonicNumber b : Complex))
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul hu (harmonicNumber_log_bound b) (harmonicNumber_nonneg b) hM)
  have hsecond : ‖Complex.exp (-u * Complex.log (1 - z))‖ ≤
      Real.exp (M * (Real.log (b : Real) + Real.log 3 + Real.pi)) := by
    calc
      _ ≤ Real.exp (‖u‖ * ‖Complex.log (1 - z)‖) := by
        simpa only [norm_mul, norm_neg] using Complex.norm_exp_le_exp_norm (-u * Complex.log (1 - z))
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul hu (norm_log_outer_bound b hb z hz) (norm_nonneg _) hM)
  calc
    _ = ‖Complex.exp (-u * (harmonicNumber b : Complex))‖ * ‖Complex.exp (-u * Complex.log (1 - z))‖ :=
      norm_mul _ _
    _ ≤ Real.exp (M * (1 + Real.log (b : Real))) *
        Real.exp (M * (Real.log (b : Real) + Real.log 3 + Real.pi)) :=
      mul_le_mul hfirst hsecond (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos hbR]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem log_outer_radius_lower (b : Nat) (hb : 0 < b) :
    1 / (2 * (b : Real)) ≤ Real.log (1 + (b : Real)⁻¹) := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hb1 : (1 : Real) ≤ b := by exact_mod_cast hb
  have hh := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + (b : Real)⁻¹)
  have heq : 1 - (1 + (b : Real)⁻¹)⁻¹ = 1 / ((b : Real) + 1) := by field_simp; ring
  rw [heq] at hh
  exact (one_div_le_one_div_of_le (by positivity) (by linarith : (b : Real) + 1 ≤ 2 * (b : Real))).trans hh

theorem outer_radius_inverse_power_decay (b N : Nat) (hb : 0 < b) :
    ((1 + (b : Real)⁻¹) ^ N)⁻¹ ≤ Real.exp (-(N : Real) / (2 * (b : Real))) := by
  have hbase : 0 < 1 + (b : Real)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_left (log_outer_radius_lower b hb) (Nat.cast_nonneg N)
  rw [← Real.rpow_natCast, ← Real.rpow_neg hbase.le, Real.rpow_def_of_pos hbase]
  apply Real.exp_le_exp.mpr
  simp only [mul_one_div] at hh
  rw [neg_div]
  nlinarith only [hh]

#print axioms harmonicPolynomial_outer_bound
#print axioms norm_log_outer_bound
#print axioms reservoirKernel_outer_polynomial_bound
#print axioms reservoirComparison_outer_polynomial_bound
#print axioms outer_radius_inverse_power_decay

end ConditionalSpectralExtremes.ReservoirAnalysis
