import CriticalPointDerivatives

/-! Uniformity on actual compact critical-parameter ranges. -/
noncomputable section
open Set
namespace ConditionalSpectralExtremes

theorem criticalPoint_continuousOn : ContinuousOn criticalPoint (Ioi 0) := by
  intro κ hκ
  exact (criticalPoint_hasDerivAt hκ).continuousAt.continuousWithinAt

theorem criticalPoint_strictAntiOn : StrictAntiOn criticalPoint (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0) criticalPoint_continuousOn
  intro κ hκ
  have hp : 0 < κ := interior_subset hκ
  rw [(criticalPoint_hasDerivAt hp).deriv]
  have hs := criticalPoint_pos hp
  have hc := lambda_deriv2_pos (by linarith : -1 < criticalPoint κ)
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem criticalPoint_compact_bounds {κlo κhi κ : ℝ}
    (hlo : 0 < κlo) (hloκ : κlo ≤ κ) (hκhi : κ ≤ κhi) :
    0 < criticalPoint κhi ∧
      criticalPoint κhi ≤ criticalPoint κ ∧ criticalPoint κ ≤ criticalPoint κlo := by
  have hκ : 0 < κ := lt_of_lt_of_le hlo hloκ
  have hhi : 0 < κhi := lt_of_lt_of_le hκ hκhi
  exact ⟨criticalPoint_pos hhi,
    criticalPoint_strictAntiOn.antitoneOn hκ hhi hκhi,
    criticalPoint_strictAntiOn.antitoneOn hlo hκ hloκ⟩

theorem lambda_curvature_continuousOn :
    ContinuousOn (deriv^[2] lambda) (Ioi (-1)) := by
  intro s hs
  exact (((lambda_contDiffAt hs 3).derivWithin (m := 2) (by norm_num)).derivWithin
    (m := 1) (by norm_num)).continuousAt.continuousWithinAt

theorem lambda_curvature_compact_bounds {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) :
    ∃ vlo vhi : ℝ, 0 < vlo ∧ ∀ s ∈ Icc a b,
      vlo ≤ (deriv^[2] lambda) s ∧ (deriv^[2] lambda) s ≤ vhi := by
  have hcont : ContinuousOn (deriv^[2] lambda) (Icc a b) :=
    lambda_curvature_continuousOn.mono (fun s hs => lt_of_lt_of_le ha hs.1)
  obtain ⟨x, hx, hxmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hcont
  obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hcont
  exact ⟨(deriv^[2] lambda) x, (deriv^[2] lambda) y,
    lambda_deriv2_pos (lt_of_lt_of_le ha hx.1), fun s hs => ⟨hxmin hs, hymax hs⟩⟩

theorem critical_curvature_uniform {κlo κhi : ℝ} (hlo : 0 < κlo) (hlohi : κlo ≤ κhi) :
    ∃ vlo vhi : ℝ, 0 < vlo ∧ ∀ κ ∈ Icc κlo κhi,
      vlo ≤ (deriv^[2] lambda) (criticalPoint κ) ∧
        (deriv^[2] lambda) (criticalPoint κ) ≤ vhi := by
  have hhi : 0 < κhi := lt_of_lt_of_le hlo hlohi
  have hslo : -1 < criticalPoint κhi := by linarith [criticalPoint_pos hhi]
  have hsorder := criticalPoint_strictAntiOn.antitoneOn hlo hhi hlohi
  obtain ⟨vlo, vhi, hpos, hb⟩ := lambda_curvature_compact_bounds hslo hsorder
  refine ⟨vlo, vhi, hpos, ?_⟩
  intro κ hκ
  exact hb _ (criticalPoint_compact_bounds hlo hκ.1 hκ.2).2

#print axioms criticalPoint_strictAntiOn
#print axioms criticalPoint_compact_bounds
#print axioms critical_curvature_uniform

end ConditionalSpectralExtremes
