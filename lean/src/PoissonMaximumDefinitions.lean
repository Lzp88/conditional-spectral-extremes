import PoissonMaximalBernstein

/-! The actual finite Poisson path maximum and its normalized tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

def poissonPrefixMaximum {q : ℕ} (α : Fin q → ℝ≥0) (ω : Fin q → ℕ) : ℝ :=
  (Finset.range (q+1)).sup' Finset.nonempty_range_add_one (fun j => |centeredPoissonPartial α j ω|)

def normalizedPoissonMaximum {q : ℕ} (α : Fin q → ℝ≥0) (ω : Fin q → ℕ) : ℝ :=
  poissonPrefixMaximum α ω/Real.sqrt (∑ i, (α i : ℝ))

theorem poissonPrefixMaximum_measurable {q : ℕ} (α : Fin q → ℝ≥0) :
    Measurable (poissonPrefixMaximum α) := by
  apply Finset.measurable_range_sup''
  intro j _
  unfold centeredPoissonPartial centeredPoisson FiniteWalk.partialSum
  fun_prop

theorem normalizedPoissonMaximum_measurable {q : ℕ} (α : Fin q → ℝ≥0) :
    Measurable (normalizedPoissonMaximum α) := (poissonPrefixMaximum_measurable α).div_const _

theorem poissonPrefixMaximum_nonneg {q : ℕ} (α : Fin q → ℝ≥0) (ω : Fin q → ℕ) :
    0 ≤ poissonPrefixMaximum α ω := by
  exact (abs_nonneg (centeredPoissonPartial α 0 ω)).trans
    (Finset.le_sup' (fun j => |centeredPoissonPartial α j ω|) (Finset.mem_range.mpr (Nat.succ_pos q)))

theorem normalizedPoissonMaximum_nonneg {q : ℕ} (α : Fin q → ℝ≥0) (ω : Fin q → ℕ) :
    0 ≤ normalizedPoissonMaximum α ω := div_nonneg (poissonPrefixMaximum_nonneg α ω) (Real.sqrt_nonneg _)

theorem poissonPrefixMaximum_ge_iff {q : ℕ} (α : Fin q → ℝ≥0) (ω : Fin q → ℕ) (w : ℝ) :
    w ≤ poissonPrefixMaximum α ω ↔ ∃ j ≤ q, w ≤ |centeredPoissonPartial α j ω| := by
  simp only [poissonPrefixMaximum, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_add_one_iff]

theorem normalizedPoissonMaximum_tail {q : ℕ} (α : Fin q → ℝ≥0)
    (hα : 1 ≤ ∑ i, (α i : ℝ)) (y : ℝ) (_hy : 0 < y) :
    (poissonProductLaw α).real {ω | y ≤ normalizedPoissonMaximum α ω} ≤
      (2*Real.exp 1)*Real.exp (-y/2) := by
  have hΛ : 0 < ∑ i, (α i : ℝ) := lt_of_lt_of_le zero_lt_one hα
  by_cases hy2 : 2 ≤ y
  · have he : {ω : Fin q → ℕ | y ≤ normalizedPoissonMaximum α ω} =
        {ω | ∃ j ≤ q, y*Real.sqrt (∑ i, (α i : ℝ)) ≤ |centeredPoissonPartial α j ω|} := by
      ext ω
      simp only [mem_ofPred_eq, normalizedPoissonMaximum,
        le_div_iff₀ (Real.sqrt_pos.mpr hΛ), poissonPrefixMaximum_ge_iff]
    rw [he]
    exact (centeredPoissonPartial_normalized_tail α hα y hy2).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)])
        (Real.exp_nonneg _))
  · have he : 1 ≤ Real.exp 1*Real.exp (-y/2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    have hp : (poissonProductLaw α).real {ω | y ≤ normalizedPoissonMaximum α ω} ≤ 1 := measureReal_le_one
    nlinarith

#print axioms poissonPrefixMaximum_measurable
#print axioms normalizedPoissonMaximum_measurable
#print axioms poissonPrefixMaximum_nonneg
#print axioms normalizedPoissonMaximum_nonneg
#print axioms poissonPrefixMaximum_ge_iff
#print axioms normalizedPoissonMaximum_tail

end ConditionalSpectralExtremes.BlockCounts
