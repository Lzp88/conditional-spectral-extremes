import CountPathEnvironment

/-! Uniform fourth moments of the actual count-path environment under
independent Poisson increments, including the centering drift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem poisson_countPathEnvironment_fourth_moment {q : ℕ} (α : Fin q → ℝ≥0) (H μ C : ℝ)
    (hH : 0 < H) (_hC : 0 ≤ C) (hα : 1 ≤ ∑ i, (α i : ℝ))
    (hαH : (∑ i, (α i : ℝ)) ≤ C*H)
    (hδ : (∑ i, |(α i : ℝ)-μ|) ≤ Real.sqrt H) :
    Integrable (fun X => (countPathEnvironment H μ X)^4) (poissonProductLaw α) ∧
      (∫ X, (countPathEnvironment H μ X)^4 ∂poissonProductLaw α) ≤ 128+6144*Real.exp 1*C^2 := by
  have hraw := poissonPrefixMaximum_fourth_moment α hα
  have hi := (integrable_const (128 : ℝ) (μ := poissonProductLaw α)).add
    ((hraw.1.const_mul 8).div_const (H^2))
  dsimp only [Pi.add_def] at hi
  have hpoint := countPathEnvironment_fourth_bound α H μ hH hδ
  have henv : Integrable (fun X => (countPathEnvironment H μ X)^4) (poissonProductLaw α) := by
    apply hi.mono' (.of_discrete)
    apply ae_of_all
    intro X
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (countPathEnvironment H μ X)^4)]
    exact hpoint X
  refine ⟨henv, ?_⟩
  have hb := integral_mono henv hi hpoint
  rw [integral_add (integrable_const _) ((hraw.1.const_mul 8).div_const (H^2)),
    integral_const, integral_div, integral_const_mul] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
  have hratio : (∑ i, (α i : ℝ))^2/H^2 ≤ C^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hH)).mpr
    have hh := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => (α i).coe_nonneg)) hαH 2
    simpa only [mul_pow] using hh
  calc
    _ ≤ 128+8*(∫ X, (poissonPrefixMaximum α X)^4 ∂poissonProductLaw α)/H^2 := hb
    _ ≤ 128+8*((768*Real.exp 1)*(∑ i, (α i : ℝ))^2)/H^2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hraw.2 (by norm_num)) (sq_nonneg H))
    _ = 128+(6144*Real.exp 1)*((∑ i, (α i : ℝ))^2/H^2) := by ring
    _ ≤ _ := add_le_add le_rfl (by
      have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 6144*Real.exp 1)
      simpa only [mul_assoc] using hh)

#print axioms poisson_countPathEnvironment_fourth_moment

end ConditionalSpectralExtremes.BlockCounts
