import FallingFactorialSaddle

/-! Exact infinite-series comparison behind the elementary marker saddle. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes

def saddleSeriesConstant : ℝ := ∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 2 : ℝ) ^ m

theorem saddleSeriesConstant_nonneg : 0 ≤ saddleSeriesConstant := by
  apply tsum_nonneg
  intro m
  positivity

theorem weighted_marker_saddle_error {j : ℕ} (hj : 1 ≤ j) {b : ℕ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ m : ℕ, ‖b m‖ ≤ M * (1 / 2 : ℝ) ^ m) :
    ‖(∑ m ∈ Finset.range (j + 1), b m * (fallingRatio j m : ℂ)) - ∑' m, b m‖ ≤
      (M / j) * saddleSeriesConstant := by
  have hbS : Summable b :=
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left M).of_norm_bounded hb
  have hw : HasSum (fun m => b m * (fallingRatio j m : ℂ))
      (∑ m ∈ Finset.range (j + 1), b m * (fallingRatio j m : ℂ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro m hm
    have hlt : j < m := by simp only [Finset.mem_range] at hm; omega
    simp [fallingRatio_eq_zero_of_lt hlt]
  have he := hw.sub hbS.hasSum
  have hterm (m : ℕ) : ‖b m * (fallingRatio j m : ℂ) - b m‖ ≤
      (M / j) * ((m : ℝ) ^ 2 * (1 / 2 : ℝ) ^ m) := by
    have hnorm : ‖(fallingRatio j m : ℂ) - 1‖ = |1 - fallingRatio j m| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, abs_sub_comm]
      exact Real.norm_eq_abs _
    rw [show b m * (fallingRatio j m : ℂ) - b m = b m * ((fallingRatio j m : ℂ) - 1) by ring,
      norm_mul, hnorm]
    calc
      ‖b m‖ * |1 - fallingRatio j m| ≤ (M * (1 / 2 : ℝ) ^ m) * ((m : ℝ) ^ 2 / j) :=
        mul_le_mul (hb m) (fallingRatio_error_le hj m) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hmS := saddle_geometric_majorant_summable.mul_left (M / j)
  have hh := he.norm_le_of_bounded hmS.hasSum hterm
  simpa only [hmS.tsum_mul_left, tsum_mul_left, saddleSeriesConstant] using hh

#print axioms weighted_marker_saddle_error
end ConditionalSpectralExtremes
