import UniformGammaCoefficient

/-! The manuscript's absolute uniform Gamma-ratio estimate. -/
noncomputable section
open Set
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis

theorem marker_error_rescale {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    markerValue n z - (n : ℂ) ^ (z - 1) / Complex.Gamma z =
      (n : ℂ) ^ (z - 1) *
        ((n : ℂ) ^ (1 - z) * markerValue n z - (Complex.Gamma z)⁻¹) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hp : (n : ℂ) ^ (z - 1) * (n : ℂ) ^ (1 - z) = 1 := by
    rw [← Complex.cpow_add _ _ hn0]
    have he : z - 1 + (1 - z) = 0 := by ring
    rw [he, Complex.cpow_zero]
  rw [mul_sub, ← mul_assoc, hp, one_mul, div_eq_mul_inv]

theorem uniform_absolute_marker_error {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖markerValue n z - (n : ℂ) ^ (z - 1) / Complex.Gamma z‖ ≤
        C * (n : ℝ) ^ (z.re - 2) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := uniform_normalized_marker_error hR
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn z hz
  have hn1 : 1 ≤ n := le_trans hN hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn1
  rw [marker_error_rescale (Nat.ne_of_gt (by omega)) z, norm_mul]
  have hnorm : ‖(n : ℂ) ^ (z - 1)‖ = (n : ℝ) ^ (z.re - 1) := by
    simpa only [Complex.sub_re, Complex.one_re, Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos hnp (z - 1)
  rw [hnorm]
  calc
    (n : ℝ) ^ (z.re - 1) * ‖(n : ℂ) ^ (1 - z) * markerValue n z - (Complex.Gamma z)⁻¹‖ ≤
      (n : ℝ) ^ (z.re - 1) * (C / n) :=
        mul_le_mul_of_nonneg_left (hbound n hn z hz) (Real.rpow_nonneg hnp.le _)
    _ = C * (n : ℝ) ^ (z.re - 2) := by
      have he : z.re - 2 = (z.re - 1) - 1 := by ring
      conv_rhs => rw [he, Real.rpow_sub hnp, Real.rpow_one]
      ring

#print axioms uniform_absolute_marker_error
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
