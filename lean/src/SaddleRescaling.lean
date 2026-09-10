import SaddleFactorialBound

/-! Exact rescaling and logarithmic control of Cauchy errors on the marker saddle circle. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem saddle_cauchy_rescaling {n : ℝ} (hn : 1 < n) {j : ℕ} (hj : 1 ≤ j) (C : ℝ) :
    (n * j.factorial / (Real.log n) ^ j) *
      (C * n ^ ((j : ℝ) / Real.log n - 2) * ((j : ℝ) / Real.log n)⁻¹ ^ j) =
      (C / n) * ((j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j) := by
  have hnp : 0 < n := zero_lt_one.trans hn
  have hL : 0 < Real.log n := Real.log_pos hn
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hexp : n ^ ((j : ℝ) / Real.log n - 2) = Real.exp j / n ^ 2 := by
    rw [Real.rpow_sub hnp, Real.rpow_two, Real.rpow_def_of_pos hnp]
    congr 2
    field_simp
  rw [hexp, inv_div, div_pow]
  field_simp

theorem saddle_cauchy_error_log_bound {n B C : ℝ} (hn : 1 < n) (hC : 0 ≤ C)
    {j : ℕ} (hj : 1 ≤ j) (hjB : (j : ℝ) / Real.log n ≤ B) :
    (C / n) * ((j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j) ≤
      (8 * C * Real.exp 1 * B) / Real.log n := by
  have hnp : 0 < n := zero_lt_one.trans hn
  have hL : 0 < Real.log n := Real.log_pos hn
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hB : 0 < B := (div_pos hjp hL).trans_le hjB
  have hjBL : (j : ℝ) ≤ B * Real.log n := (div_le_iff₀ hL).1 hjB
  have hlog := log_sq_le_four_mul hn.le
  calc
    _ ≤ (C / n) * (2 * Real.exp 1 * j) :=
      mul_le_mul_of_nonneg_left (factorial_saddle_bound hj) (by positivity)
    _ ≤ (C / n) * (2 * Real.exp 1 * (B * Real.log n)) := by gcongr
    _ ≤ (8 * C * Real.exp 1 * B) / Real.log n := by
      apply (le_div_iff₀ hL).2
      have he : C / n * (2 * Real.exp 1 * (B * Real.log n)) * Real.log n =
          (2 * C * Real.exp 1 * B / n) * (Real.log n) ^ 2 := by ring
      rw [he]
      calc
        _ ≤ (2 * C * Real.exp 1 * B / n) * (4 * n) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by field_simp; ring

#print axioms saddle_cauchy_error_log_bound
end ConditionalSpectralExtremes
