import SaddleFactorialBound

/-! The square-root factorial loss required for the reservoir saddle error. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem factorial_saddle_sqrt_bound {j : ℕ} (hj : 1 ≤ j) :
    (j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j ≤ Real.exp 1 * Real.sqrt (2 * j) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hs : Stirling.stirlingSeq j ≤ Real.exp 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    have he := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at he
    exact he.trans (div_le_self (Real.exp_pos _).le (by norm_num : (1 : ℝ) ≤ Real.sqrt 2))
  have he : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by simp
  have hident : (j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j =
      Stirling.stirlingSeq j * Real.sqrt (2 * j) := by
    rw [Stirling.stirlingSeq, he, div_pow]
    field_simp
  rw [hident]
  exact mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)

#print axioms factorial_saddle_sqrt_bound
end ConditionalSpectralExtremes
