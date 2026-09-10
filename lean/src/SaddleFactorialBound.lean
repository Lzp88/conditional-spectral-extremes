import Mathlib

/-! Quantitative factorial and logarithm bounds used when transferring analytic error. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem factorial_saddle_bound {j : ℕ} (hj : 1 ≤ j) :
    (j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j ≤ 2 * Real.exp 1 * j := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hs : Stirling.stirlingSeq j ≤ Real.exp 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    have he := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at he
    exact he.trans ((div_le_self (Real.exp_pos _).le (by norm_num : (1 : ℝ) ≤ Real.sqrt 2)))
  have hsq : Real.sqrt (2 * (j : ℝ)) ≤ 2 * j := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have he : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    simp
  have hident : (j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j =
      Stirling.stirlingSeq j * Real.sqrt (2 * j) := by
    rw [Stirling.stirlingSeq, he, div_pow]
    field_simp
  rw [hident]
  calc
    _ ≤ Real.exp 1 * Real.sqrt (2 * j) := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ ≤ Real.exp 1 * (2 * j) := mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = _ := by ring

theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 4 * x := by
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hxp)
  rw [Real.log_sqrt hxp.le] at hs
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsq := Real.sq_sqrt hxp.le
  nlinarith [Real.sqrt_nonneg x]

#print axioms factorial_saddle_bound
#print axioms log_sq_le_four_mul
end ConditionalSpectralExtremes
