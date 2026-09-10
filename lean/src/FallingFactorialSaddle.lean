import Mathlib

/-! A uniform falling-factorial bound for the elementary marker saddle. -/
noncomputable section
namespace ConditionalSpectralExtremes

def fallingRatio (j m : ℕ) : ℝ := (j.descFactorial m : ℝ) / (j : ℝ) ^ m

theorem fallingRatio_bounds {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    0 ≤ fallingRatio j m ∧ fallingRatio j m ≤ 1 := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  constructor
  · unfold fallingRatio; positivity
  · unfold fallingRatio
    apply (div_le_one (pow_pos hjp m)).2
    exact_mod_cast Nat.descFactorial_le_pow j m

theorem fallingRatio_succ {j m : ℕ} (hj : 1 ≤ j) (hm : m ≤ j) :
    fallingRatio j (m + 1) = fallingRatio j m * (1 - (m : ℝ) / j) := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  simp only [fallingRatio, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hm, pow_succ]
  field_simp

theorem fallingRatio_error_le {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    |1 - fallingRatio j m| ≤ (m : ℝ) ^ 2 / j := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  rw [abs_of_nonneg (sub_nonneg.2 (fallingRatio_bounds hj m).2)]
  by_cases hm : m ≤ j
  · induction m with
    | zero => simp [fallingRatio]
    | succ m ih =>
      have hmj : m ≤ j := by omega
      have hih := ih hmj
      rw [fallingRatio_succ hj hmj]
      have hratio := fallingRatio_bounds hj m
      have hmul := mul_le_mul_of_nonneg_left hratio.2 (show 0 ≤ (m : ℝ) / j by positivity)
      calc
        1 - fallingRatio j m * (1 - (m : ℝ) / j) ≤ (m : ℝ) ^ 2 / j + (m : ℝ) / j := by
          nlinarith
        _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 / j := by
          rw [← add_div]
          apply (div_le_div_iff_of_pos_right hjp).2
          push_cast
          nlinarith
  · have hjm : j < m := lt_of_not_ge hm
    have hz : j.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hjm
    simp only [fallingRatio, hz, Nat.cast_zero, zero_div, sub_zero]
    apply (one_le_div hjp).2
    have hcast : (j : ℝ) < m := by exact_mod_cast hjm
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith

theorem fallingRatio_eq_zero_of_lt {j m : ℕ} (h : j < m) : fallingRatio j m = 0 := by
  simp [fallingRatio, Nat.descFactorial_eq_zero_iff_lt.2 h]

theorem saddle_geometric_majorant_summable :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * (1 / 2 : ℝ) ^ m) :=
  summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)

#print axioms fallingRatio_error_le
#print axioms saddle_geometric_majorant_summable
end ConditionalSpectralExtremes
