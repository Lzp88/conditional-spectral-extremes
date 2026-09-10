import CountPathEnvironment

/-! The actual count-environment maximum has a Gaussian moderate tail,
uniform over all Poisson rates with controlled total rate and centering drift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem poisson_countPathEnvironment_tail {q : ℕ} (α : Fin q → ℝ≥0) (H μ C : ℝ)
    (hH : 0 < H) (hC : 1 ≤ C) (hα : 0 < ∑ i, (α i : ℝ))
    (hαH : (∑ i, (α i : ℝ)) ≤ C*H)
    (hδ : (∑ i, |(α i : ℝ)-μ|) ≤ Real.sqrt H)
    (x : ℝ) (hx : 2 ≤ x) (hxH : x-2 ≤ Real.sqrt H) :
    (poissonProductLaw α).real {X | x ≤ countPathEnvironment H μ X} ≤
      2*Real.exp (-(x-2)^2/(4*C)) := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let w : ℝ := (x-2)*Real.sqrt H
  have hw : 0 ≤ w := mul_nonneg (sub_nonneg.mpr hx) hs.le
  have hsub : {X : Fin q → ℕ | x ≤ countPathEnvironment H μ X} ⊆
      {X | ∃ j ≤ q, w ≤ |centeredPoissonPartial α j X|} := by
    intro X hX
    change x ≤ countPathEnvironment H μ X at hX
    apply (poissonPrefixMaximum_ge_iff α X w).mp
    have hE := countPathEnvironment_poisson_bound α H μ hH hδ X
    have hh : x-2 ≤ poissonPrefixMaximum α X/Real.sqrt H := by linarith
    exact (le_div_iff₀ hs).mp hh
  have hp := (measureReal_mono hsub).trans
    (centeredPoissonPartial_maximal_bernstein α hα w hw)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have h1 : (x-2)^2/(4*C) ≤ w^2/(4*(∑ i, (α i : ℝ))) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*C) (by positivity : 0 < 4*(∑ i, (α i : ℝ)))).mpr
    have hh := mul_le_mul_of_nonneg_left hαH (sq_nonneg (x-2))
    have hw2 : w^2 = (x-2)^2*H := by rw [show w = (x-2)*Real.sqrt H from rfl, mul_pow, Real.sq_sqrt hH.le]
    rw [hw2]
    nlinarith
  have h2 : (x-2)^2/(4*C) ≤ w/2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*C) (by norm_num : (0 : ℝ) < 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hxH (sub_nonneg.mpr hx)
    have hc := mul_le_mul_of_nonneg_right hC hw
    dsimp only [w] at hc ⊢
    nlinarith
  have hh := le_min h1 h2
  rw [neg_div]
  exact neg_le_neg hh

#print axioms poisson_countPathEnvironment_tail

end ConditionalSpectralExtremes.BlockCounts
