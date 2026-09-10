import AnalyticCoefficientBounds
import WeightedMarkerSaddle
import MarkerSaddleAlgebra

/-! Uniform elementary saddle estimate for an actual entire marker function. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes
open ReservoirAnalysis

theorem entire_marker_saddle {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (j : ℕ), 0 < x → 1 ≤ j →
      a ≤ (j : ℝ) / x → (j : ℝ) / x ≤ B →
      ‖((j.factorial : ℂ) / (x : ℂ) ^ j) *
          analyticCoefficient (fun z => Complex.exp ((x : ℂ) * z) * g z) j -
        g (((j : ℝ) / x : ℝ) : ℂ)‖ ≤ C / x := by
  have hB : 0 < B := ha.trans_le haB
  let M := circleCoefficientBound g (2 * B)
  have hM : 0 ≤ M := circleCoefficientBound_nonneg _ _
  have hS : 0 ≤ saddleSeriesConstant := saddleSeriesConstant_nonneg
  refine ⟨M * saddleSeriesConstant / a, by positivity, ?_⟩
  intro x j hx hj haj hjB
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hκ : 0 ≤ (j : ℝ) / x := by positivity
  let b : ℕ → ℂ := fun m => analyticCoefficient g m * (((j : ℝ) / x : ℝ) : ℂ) ^ m
  have hb (m : ℕ) : ‖b m‖ ≤ M * (1 / 2 : ℝ) ^ m := by
    dsimp [b]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
    calc
      ‖analyticCoefficient g m‖ * ((j : ℝ) / x) ^ m ≤
          (M * (2 * B)⁻¹ ^ m) * ((j : ℝ) / x) ^ m :=
        mul_le_mul_of_nonneg_right (entire_analyticCoefficient_bound hg (by positivity) m)
          (pow_nonneg hκ _)
      _ = M * (((j : ℝ) / x) / (2 * B)) ^ m := by rw [div_eq_mul_inv, mul_pow]; ring
      _ ≤ M * (1 / 2 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply pow_le_pow_left₀ (by positivity)
        apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
        linarith
  have he := weighted_marker_saddle_error hj hM hb
  have hs : ∑' m, b m = g (((j : ℝ) / x : ℝ) : ℂ) :=
    (entire_hasSum_analyticCoefficient hg _).tsum_eq
  rw [hs] at he
  have hjx : a * x ≤ (j : ℝ) := (le_div_iff₀ hx).1 haj
  calc
    _ = ‖(∑ m ∈ Finset.range (j + 1), b m * (fallingRatio j m : ℂ)) -
        g (((j : ℝ) / x : ℝ) : ℂ)‖ := by
      rw [normalized_exp_marker_coefficient hg hj hx]
      simp only [b, Complex.ofReal_div, Complex.ofReal_natCast]
    _ ≤ (M / j) * saddleSeriesConstant := he
    _ ≤ (M / (a * x)) * saddleSeriesConstant :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hM (mul_pos ha hx) hjx)
        saddleSeriesConstant_nonneg
    _ = (M * saddleSeriesConstant / a) / x := by ring

#print axioms entire_marker_saddle
end ConditionalSpectralExtremes
