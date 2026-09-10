import TiltedLogSine

/-! Continuity and compact uniform bounds for actual centered absolute moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem lambda_mean_continuousOn (a b : ℝ) (ha : -1 < a) :
    ContinuousOn (deriv lambda) (Icc a b) := by
  intro β hβ
  exact (((lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 1).derivWithin
    (m := 0) (by norm_num)).continuousAt).continuousWithinAt

theorem tiltedLogSineLaw_centered_moment_eq {β : ℝ} (hβ : -1 < β) (p : ℕ) :
    (∫ x, ‖centeredLogSine β x‖ ^ p ∂tiltedLogSineLaw β) =
      Real.exp (-lambda β) *
        ∫ x, Real.exp (β*x) * ‖x - deriv lambda β‖ ^ p ∂logSineLaw := by
  change (∫ x, ‖centeredLogSine β x‖ ^ p ∂logSineLaw.tilted (fun x => β * id x)) = _
  rw [integral_tilted_mul_eq_cgf (X := id) _ (logSineLaw_exp_integrable β hβ),
    logSineLaw_cgf β hβ, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [centeredLogSine, smul_eq_mul, id_eq, Real.exp_sub, Real.exp_neg]
  ring

theorem logSineLaw_weighted_norm_add_pow_integrable {β : ℝ} (hβ : -1 < β)
    (M : ℝ) (hM : 0 ≤ M) (p : ℕ) :
    Integrable (fun x => Real.exp (β*x) * (‖x‖ + M)^p) logSineLaw := by
  let : IsProbabilityMeasure (tiltedLogSineLaw β) := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hm : MemLp (fun x : ℝ => ‖x‖ + M) p (tiltedLogSineLaw β) :=
    ((tiltedLogSineLaw_all_moments β hβ p).norm).add (memLp_const M)
  have hi := hm.integrable_norm_pow'
  simp only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hM)] at hi
  exact (integrable_tilted_iff (logSineLaw_exp_integrable β hβ) _).mp hi

theorem tiltedLogSineLaw_centered_moment_continuousOn
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (p : ℕ) :
    ContinuousOn (fun β => ∫ x, ‖centeredLogSine β x‖^p ∂tiltedLogSineLaw β) (Icc a b) := by
  have hmean := lambda_mean_continuousOn a b ha
  obtain ⟨β₀, hβ₀, hM⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hmean.norm
  let M : ℝ := ‖deriv lambda β₀‖
  have hMn : 0 ≤ M := norm_nonneg _
  have hc : ContinuousOn (fun β => ∫ x, Real.exp (β*x) * ‖x - deriv lambda β‖^p ∂logSineLaw)
      (Icc a b) := by
    apply continuousOn_of_dominated
      (bound := fun x => (Real.exp (a*x) + Real.exp (b*x)) * (‖x‖ + M)^p)
    · intro β hβ
      exact (show Continuous (fun x : ℝ => Real.exp (β*x) * ‖x - deriv lambda β‖^p) by
        fun_prop).aestronglyMeasurable
    · intro β hβ
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (norm_nonneg _) _))]
      have he : Real.exp (β*x) ≤ Real.exp (a*x) + Real.exp (b*x) := by
        by_cases hx : 0 ≤ x
        · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.2 hx)).trans
            (le_add_of_nonneg_left (Real.exp_pos _).le)
        · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hβ.1 (le_of_not_ge hx))).trans
            (le_add_of_nonneg_right (Real.exp_pos _).le)
      apply mul_le_mul he
      · have hmβ : ‖deriv lambda β‖ ≤ M := hM hβ
        exact pow_le_pow_left₀ (norm_nonneg (x - deriv lambda β))
          ((norm_sub_le x (deriv lambda β)).trans (add_le_add le_rfl hmβ)) p
      · exact pow_nonneg (norm_nonneg _) _
      · positivity
    · convert (logSineLaw_weighted_norm_add_pow_integrable ha M hMn p).add
        (logSineLaw_weighted_norm_add_pow_integrable (lt_of_lt_of_le ha hab) M hMn p) using 1
      all_goals first | rfl | (ext x; simp only [Pi.add_apply, add_mul])
    · apply Filter.Eventually.of_forall
      intro x
      exact ((continuousOn_id.mul continuousOn_const).rexp).mul
        ((continuousOn_const.sub hmean).norm.pow p)
  have hl : ContinuousOn (fun β => Real.exp (-lambda β)) (Icc a b) := by
    intro β hβ
    exact ((lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 0).continuousAt.neg.rexp).continuousWithinAt
  exact (hl.mul hc).congr (fun β hβ =>
    tiltedLogSineLaw_centered_moment_eq (lt_of_lt_of_le ha hβ.1) p)

theorem tiltedLogSineLaw_centered_moment_uniform_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Icc a b,
      (∫ x, ‖centeredLogSine β x‖^p ∂tiltedLogSineLaw β) ≤ C := by
  obtain ⟨β₀, hβ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    (tiltedLogSineLaw_centered_moment_continuousOn a b ha hab p)
  exact ⟨_, integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _), fun β hβ => hmax hβ⟩

#print axioms lambda_mean_continuousOn
#print axioms tiltedLogSineLaw_centered_moment_eq
#print axioms logSineLaw_weighted_norm_add_pow_integrable
#print axioms tiltedLogSineLaw_centered_moment_continuousOn
#print axioms tiltedLogSineLaw_centered_moment_uniform_bound

end ConditionalSpectralExtremes
