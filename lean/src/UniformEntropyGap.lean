import LambdaEntropyGap

/-! Compact uniform entropy gap, including the count-envelope slack eta. -/
noncomputable section
open Set
namespace ConditionalSpectralExtremes

theorem entropyCost_eq_clamped (s : ℝ) :
    entropyCost s = (max s 2-1)*Real.log 2-lambda (max s 2) := by
  by_cases hs : s ≤ 2
  · norm_num [entropyCost, hs, lambda_two]
  · simp [entropyCost, hs, max_eq_left (le_of_not_ge hs)]

theorem entropyCost_continuous : Continuous entropyCost := by
  have hm : Continuous (fun s : ℝ => max s 2) := continuous_id.max continuous_const
  have hl : Continuous (fun s : ℝ => lambda (max s 2)) :=
    lambda_continuousOn.comp_continuous hm (fun s => by
      have := le_max_right s (2 : ℝ)
      change -1 < max s 2
      linarith)
  simp_rw [funext entropyCost_eq_clamped]
  exact ((hm.sub continuous_const).mul continuous_const).sub hl

theorem criticalEntropy_continuousOn :
    ContinuousOn (fun κ => κ*entropyCost (criticalPoint κ)) (Ioi 0) :=
  continuousOn_id.mul (entropyCost_continuous.comp_continuousOn criticalPoint_continuousOn)

theorem actual_uniform_entropy_gap {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ κ ∈ Icc a B,
      (κ+η)*entropyCost (criticalPoint κ) ≤ ρ := by
  have hsub : Icc a B ⊆ Ioi 0 := fun κ hκ => ha.trans_le hκ.1
  have hc := criticalEntropy_continuousOn.mono hsub
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 haB) hc
  have hxgap := actual_entropy_gap (ha.trans_le hx.1)
  have hbcont : ContinuousOn (fun κ => entropyCost (criticalPoint κ)) (Icc a B) :=
    (entropyCost_continuous.comp_continuousOn criticalPoint_continuousOn).mono hsub
  obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 haB) hbcont
  let r := max 0 (x*entropyCost (criticalPoint x))
  let M := max 1 (entropyCost (criticalPoint y))
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r < 1 := max_lt (by norm_num) hxgap
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  refine ⟨(1-r)/(2*M), (r+1)/2, by positivity, by positivity, by linarith, ?_⟩
  intro κ hκ
  have hκr : κ*entropyCost (criticalPoint κ) ≤ r := (hxmax hκ).trans (le_max_right _ _)
  have hκM : entropyCost (criticalPoint κ) ≤ M := (hymax hκ).trans (le_max_right _ _)
  have hη : 0 ≤ (1-r)/(2*M) := by positivity
  have hh := mul_le_mul_of_nonneg_left hκM hη
  have he : (1-r)/(2*M)*M=(1-r)/2 := by field_simp
  rw [he] at hh
  nlinarith

#print axioms actual_uniform_entropy_gap
end ConditionalSpectralExtremes
