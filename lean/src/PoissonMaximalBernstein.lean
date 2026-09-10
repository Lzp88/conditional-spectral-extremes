import PoissonProductMaximal

/-! Actual two-sided maximal Bernstein tails for nonidentical Poisson
increments, followed by a uniform normalized exponential tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem centeredPoissonPartial_signed_quadratic {q : ℕ} (α : Fin q → ℝ≥0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t w : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (poissonProductLaw α).real {ω | ∃ j ≤ q, w ≤ σ*centeredPoissonPartial α j ω} ≤
      Real.exp (-t*w+(∑ i, (α i : ℝ))*t^2) := by
  have hs : |σ*t| ≤ 1 := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul, abs_of_nonneg ht] using ht1
    · simpa only [neg_one_mul, abs_neg, abs_of_nonneg ht] using ht1
  have hsq : (σ*t)^2 = t^2 := by rcases hσ with rfl | rfl <;> ring
  have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hs)).2
  rw [hsq] at hh
  have hsum : 0 ≤ ∑ i, (α i : ℝ) := Finset.sum_nonneg (fun i _ => (α i).coe_nonneg)
  exact (centeredPoissonPartial_signed_maximal α σ t w ht).trans
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hh hsum]))

theorem centeredPoissonPartial_signed_bernstein {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 0 < ∑ i, (α i : ℝ)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (w : ℝ) (hw : 0 ≤ w) :
    (poissonProductLaw α).real {ω | ∃ j ≤ q, w ≤ σ*centeredPoissonPartial α j ω} ≤
      Real.exp (-min (w^2/(4*(∑ i, (α i : ℝ)))) (w/2)) := by
  let Λ := ∑ i, (α i : ℝ)
  by_cases hl : w ≤ 2*Λ
  · have ht : 0 ≤ w/(2*Λ) := by positivity
    have ht1 : w/(2*Λ) ≤ 1 := (div_le_one (by positivity)).mpr hl
    have hh := centeredPoissonPartial_signed_quadratic α σ hσ (w/(2*Λ)) w ht ht1
    have he : -(w/(2*Λ))*w+Λ*(w/(2*Λ))^2 = -w^2/(4*Λ) := by field_simp; ring
    have hmin : w^2/(4*Λ) ≤ w/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*Λ)).mpr
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hl)]
    change _ ≤ Real.exp (-min (w^2/(4*Λ)) (w/2))
    rw [min_eq_left hmin]
    change _ ≤ Real.exp (-(w/(2*Λ))*w+Λ*(w/(2*Λ))^2) at hh
    rw [he] at hh
    simpa only [neg_div] using hh
  · have hlarge : 2*Λ < w := lt_of_not_ge hl
    have hh := centeredPoissonPartial_signed_quadratic α σ hσ 1 w (by norm_num) (by norm_num)
    have hmin : w/2 ≤ w^2/(4*Λ) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*Λ)).mpr
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hlarge.le)]
    change _ ≤ Real.exp (-min (w^2/(4*Λ)) (w/2))
    rw [min_eq_right hmin]
    exact hh.trans (Real.exp_le_exp.mpr (by change -(1 : ℝ)*w+Λ*1^2 ≤ -(w/2); nlinarith))

theorem centeredPoissonPartial_maximal_bernstein {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 0 < ∑ i, (α i : ℝ)) (w : ℝ) (hw : 0 ≤ w) :
    (poissonProductLaw α).real {ω | ∃ j ≤ q, w ≤ |centeredPoissonPartial α j ω|} ≤
      2*Real.exp (-min (w^2/(4*(∑ i, (α i : ℝ)))) (w/2)) := by
  have hp := centeredPoissonPartial_signed_bernstein α hα 1 (Or.inl rfl) w hw
  have hn := centeredPoissonPartial_signed_bernstein α hα (-1) (Or.inr rfl) w hw
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  have he : {ω : Fin q → ℕ | ∃ j ≤ q, w ≤ |centeredPoissonPartial α j ω|} =
      {ω | ∃ j ≤ q, w ≤ centeredPoissonPartial α j ω} ∪
      {ω | ∃ j ≤ q, w ≤ -centeredPoissonPartial α j ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs]
    aesop
  rw [he]
  exact (measureReal_union_le _ _).trans ((add_le_add hp hn).trans_eq (by ring))

theorem centeredPoissonPartial_normalized_tail {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 1 ≤ ∑ i, (α i : ℝ)) (y : ℝ) (hy : 2 ≤ y) :
    (poissonProductLaw α).real {ω | ∃ j ≤ q,
      y*Real.sqrt (∑ i, (α i : ℝ)) ≤ |centeredPoissonPartial α j ω|} ≤ 2*Real.exp (-y/2) := by
  let Λ := ∑ i, (α i : ℝ)
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hα
  have hy0 : 0 ≤ y := by linarith
  have hs : 1 ≤ Real.sqrt Λ := (Real.one_le_sqrt).mpr hα
  have he : (y*Real.sqrt Λ)^2/(4*Λ) = y^2/4 := by
    rw [mul_pow, Real.sq_sqrt hΛ.le]
    field_simp
  have hmin : y/2 ≤ min ((y*Real.sqrt Λ)^2/(4*Λ)) (y*Real.sqrt Λ/2) := by
    rw [he]
    exact le_min (by nlinarith) (by nlinarith)
  have hh := centeredPoissonPartial_maximal_bernstein α hΛ (y*Real.sqrt Λ) (by positivity)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by have := neg_le_neg hmin; linarith)) (by norm_num))

#print axioms centeredPoissonPartial_signed_quadratic
#print axioms centeredPoissonPartial_signed_bernstein
#print axioms centeredPoissonPartial_maximal_bernstein
#print axioms centeredPoissonPartial_normalized_tail

end ConditionalSpectralExtremes.BlockCounts
