import ExponentialTailFourthMoment
import PoissonMaximumDefinitions

/-! Uniform fourth moments of the actual finite independent Poisson path maximum.
The constant follows by integrating the proved maximal tail, with no moment assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem normalizedPoissonMaximum_fourth_moment {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 1 ≤ ∑ i, (α i : ℝ)) :
    Integrable (fun ω => (normalizedPoissonMaximum α ω)^4) (poissonProductLaw α) ∧
    (∫ ω, (normalizedPoissonMaximum α ω)^4 ∂poissonProductLaw α) ≤ 768*Real.exp 1 := by
  have hh := fourth_moment_of_exponential_tail (poissonProductLaw α)
    (normalizedPoissonMaximum α) (normalizedPoissonMaximum_measurable α)
    (normalizedPoissonMaximum_nonneg α) (2*Real.exp 1) (by positivity)
    (normalizedPoissonMaximum_tail α hα)
  exact ⟨hh.1, by nlinarith [hh.2]⟩

theorem poissonPrefixMaximum_fourth_moment {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 1 ≤ ∑ i, (α i : ℝ)) :
    Integrable (fun ω => (poissonPrefixMaximum α ω)^4) (poissonProductLaw α) ∧
    (∫ ω, (poissonPrefixMaximum α ω)^4 ∂poissonProductLaw α) ≤
      (768*Real.exp 1)*(∑ i, (α i : ℝ))^2 := by
  let Λ : ℝ := ∑ i, (α i : ℝ)
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hα
  have hs : Real.sqrt Λ ^ 4 = Λ^2 := by
    calc
      _ = (Real.sqrt Λ ^ 2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hΛ.le]
  have he : (fun ω => (poissonPrefixMaximum α ω)^4) =
      fun ω => Λ^2*(normalizedPoissonMaximum α ω)^4 := by
    funext ω
    dsimp only [normalizedPoissonMaximum]
    change _ = Λ^2*(poissonPrefixMaximum α ω / Real.sqrt Λ)^4
    rw [div_pow, hs]
    field_simp
  have hh := normalizedPoissonMaximum_fourth_moment α hα
  rw [he]
  refine ⟨hh.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg Λ)
  simpa only [mul_comm (Λ^2)] using hb

#print axioms normalizedPoissonMaximum_fourth_moment
#print axioms poissonPrefixMaximum_fourth_moment

end ConditionalSpectralExtremes.BlockCounts
