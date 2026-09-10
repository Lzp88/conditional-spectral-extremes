import Mathlib

/-! Quantitative algebra for normalized characteristic kernels and all powers. -/
noncomputable section

namespace ConditionalSpectralAudit.FourierHarmonic

theorem unit_disk_power_difference (z w : Complex) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (q : Nat) : ‖z ^ q - w ^ q‖ ≤ q * ‖z - w‖ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hpow : ‖z ^ q‖ ≤ 1 := by simpa only [norm_pow, one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz q
    calc
      ‖z ^ (q + 1) - w ^ (q + 1)‖ = ‖z ^ q * (z - w) + (z ^ q - w ^ q) * w‖ := by
        congr 1
        rw [pow_succ, pow_succ]
        ring
      _ ≤ ‖z ^ q * (z - w)‖ + ‖(z ^ q - w ^ q) * w‖ := norm_add_le _ _
      _ = ‖z ^ q‖ * ‖z - w‖ + ‖z ^ q - w ^ q‖ * ‖w‖ := by simp only [norm_mul]
      _ ≤ 1 * ‖z - w‖ + (q * ‖z - w‖) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (by positivity))
      _ = _ := by push_cast; ring

theorem normalized_kernel_difference (z w : Complex) (b a E : Real)
    (hb : 0 < b) (ha : 0 < a) (hw : ‖w‖ ≤ a)
    (hzw : ‖z - w‖ ≤ E) (hba : |b - a| ≤ E) :
    ‖z / (b : Complex) - w / (a : Complex)‖ ≤ 2 * E / b := by
  have hbc : (b : Complex) ≠ 0 := by exact_mod_cast hb.ne'
  have hac : (a : Complex) ≠ 0 := by exact_mod_cast ha.ne'
  have he : z / (b : Complex) - w / (a : Complex) =
      ((z - w) + (w / (a : Complex)) * ((a : Complex) - b)) / (b : Complex) := by
    field_simp
    ring
  have hn : ‖w / (a : Complex)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (div_le_one ha).mpr hw
  have hnba : ‖(a : Complex) - b‖ ≤ E := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hba
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  apply (div_le_div_iff_of_pos_right hb).mpr
  calc
    _ ≤ ‖z - w‖ + ‖w / (a : Complex) * ((a : Complex) - b)‖ := norm_add_le _ _
    _ = ‖z - w‖ + ‖w / (a : Complex)‖ * ‖(a : Complex) - b‖ := by rw [norm_mul]
    _ ≤ E + 1 * E := add_le_add hzw (mul_le_mul hn hnba (norm_nonneg _) (by norm_num))
    _ = _ := by ring

theorem normalized_kernel_power_difference (z w : Complex) (b a E : Real)
    (hb : 0 < b) (ha : 0 < a) (hz : ‖z / (b : Complex)‖ ≤ 1)
    (hw : ‖w‖ ≤ a) (hzw : ‖z - w‖ ≤ E) (hba : |b - a| ≤ E) (q : Nat) :
    ‖(z / (b : Complex)) ^ q - (w / (a : Complex)) ^ q‖ ≤ 2 * q * E / b := by
  have hn : ‖w / (a : Complex)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (div_le_one ha).mpr hw
  calc
    _ ≤ q * ‖z / (b : Complex) - w / (a : Complex)‖ := unit_disk_power_difference _ _ hz hn q
    _ ≤ q * (2 * E / b) := mul_le_mul_of_nonneg_left
      (normalized_kernel_difference z w b a E hb ha hw hzw hba) (Nat.cast_nonneg q)
    _ = _ := by ring

#print axioms normalized_kernel_power_difference
end ConditionalSpectralAudit.FourierHarmonic
