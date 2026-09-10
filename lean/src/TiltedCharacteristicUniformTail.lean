import TiltedCharacteristicL6
import TiltedLogSineNonlattice

/-! Compact-tilt uniform frequency-tail control for the actual characteristic
function, using continuity of its sixth-power mass and Dini's theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem tiltedDensityTriple_compact_L2_envelope (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ F : ℝ → ℝ, MemLp F 2 volume ∧ (∀ x, 0 ≤ F x) ∧
      ∀ β ∈ Icc a b, ∀ x, ‖tiltedDensityTriple β x‖ ≤ F x := by
  have hc : ContinuousOn (fun β : ℝ => Real.exp (-3 * lambda β)) (Icc a b) := by
    intro β hβ
    exact ((continuousAt_const.mul
      (lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 0).continuousAt).rexp).continuousWithinAt
  obtain ⟨β₀, hβ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  let F : ℝ → ℝ := fun x => Real.exp (-3 * lambda β₀) *
    (Real.exp (3 * lambda a) * tiltedDensityTriple a x +
      Real.exp (3 * lambda b) * tiltedDensityTriple b x)
  refine ⟨F, ?_, ?_, ?_⟩
  · exact (((tiltedDensityTriple_memLp_two ha).const_mul (Real.exp (3 * lambda a))).add
      ((tiltedDensityTriple_memLp_two (lt_of_lt_of_le ha hab)).const_mul
        (Real.exp (3 * lambda b)))).const_mul (Real.exp (-3 * lambda β₀))
  · intro x
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg
      (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg a x))
      (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg b x)))
  · intro β hβ x
    rw [Real.norm_of_nonneg (tiltedDensityTriple_nonneg β x)]
    apply (tiltedDensityTriple_endpoint_domination hβ x).trans
    apply mul_le_mul_of_nonneg_right (hmax hβ)
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg a x))
      (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg b x))

theorem tiltedDensityTriple_parameter_continuousOn (a b : ℝ) (ha : -1 < a) (_hab : a ≤ b)
    (x : ℝ) : ContinuousOn (fun β => tiltedDensityTriple β x) (Icc a b) := by
  intro β hβ
  have hl := (lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 0).continuousAt
  have hc : ContinuousAt (fun γ => Real.exp (γ * x - 3 * lambda γ) * tiltedDensityTriple 0 x) β :=
    ((continuousAt_id.mul continuousAt_const).sub (continuousAt_const.mul hl)).rexp.mul
      continuousAt_const
  exact hc.continuousWithinAt.congr (fun γ _ => tiltedDensityTriple_exp_tilt γ x)
    (tiltedDensityTriple_exp_tilt β x)

theorem tiltedDensityTriple_square_integral_continuousOn
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ContinuousOn (fun β => ∫ x, tiltedDensityTriple β x ^ 2) (Icc a b) := by
  obtain ⟨F, hF, hFn, hb⟩ := tiltedDensityTriple_compact_L2_envelope a b ha hab
  apply continuousOn_of_dominated (bound := fun x => F x ^ 2)
  · intro β hβ
    exact ((tiltedDensityTriple_continuous (lt_of_lt_of_le ha hβ.1)).pow 2).aestronglyMeasurable
  · intro β hβ
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (tiltedDensityTriple_nonneg β x) (hFn x)).mpr
      (by simpa only [Real.norm_of_nonneg (tiltedDensityTriple_nonneg β x)] using hb β hβ x)
  · exact hF.integrable_sq
  · apply Eventually.of_forall
    intro x
    exact (tiltedDensityTriple_parameter_continuousOn a b ha hab x).pow 2

theorem tiltedLogSineLaw_charFun_six_mass_continuousOn
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ContinuousOn (fun β => ∫ t, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) (Icc a b) := by
  have hc : ContinuousOn (fun β => 2 * Real.pi * ∫ x, tiltedDensityTriple β x ^ 2) (Icc a b) :=
    continuousOn_const.mul (tiltedDensityTriple_square_integral_continuousOn a b ha hab)
  exact hc.congr (fun β hβ => (tiltedLogSineLaw_charFun_six_integral
    (lt_of_lt_of_le ha hβ.1)))

theorem tiltedLogSineLaw_charFun_six_truncated_continuousOn
    (a b R : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ContinuousOn (fun β => ∫ t in Icc (-R) R, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6)
      (Icc a b) := by
  apply continuousOn_of_dominated (bound := fun _ : ℝ => (1 : ℝ))
  · intro β hβ
    let : IsProbabilityMeasure (tiltedLogSineLaw β) :=
      tiltedLogSineLaw_isProbabilityMeasure β (lt_of_lt_of_le ha hβ.1)
    exact (continuous_charFun.norm.pow 6).aestronglyMeasurable
  · intro β hβ
    let : IsProbabilityMeasure (tiltedLogSineLaw β) :=
      tiltedLogSineLaw_isProbabilityMeasure β (lt_of_lt_of_le ha hβ.1)
    apply Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one t)
  · exact integrable_const 1
  · apply Eventually.of_forall
    intro t
    have hc₀ := tiltedLogSineLaw_charFun_continuousOn_strip a b ha hab
    have hc₁ : ContinuousOn (fun β : ℝ => (β, t)) (Icc a b) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc : ContinuousOn (fun β => charFun (tiltedLogSineLaw β) t) (Icc a b) :=
      hc₀.comp (g := fun p : ℝ × ℝ => charFun (tiltedLogSineLaw p.1) p.2)
        (f := fun β : ℝ => (β, t)) hc₁ (fun β hβ => ⟨hβ, mem_univ t⟩)
    exact hc.norm.pow 6

theorem tiltedLogSineLaw_charFun_six_truncated_tendsto {β : ℝ} (hβ : -1 < β) :
    Tendsto (fun n : ℕ => ∫ t in Icc (-(n : ℝ)) n, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6)
      atTop (𝓝 (∫ t, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6)) := by
  exact (aecover_Icc (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    tendsto_natCast_atTop_atTop).integral_tendsto_of_countably_generated
      (tiltedLogSineLaw_charFun_six_integrable hβ)

theorem tiltedLogSineLaw_charFun_six_truncated_uniform
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun n : ℕ => fun β => ∫ t in Icc (-(n : ℝ)) n, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6)
      (fun β => ∫ t, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) atTop (Icc a b) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (fun n : ℕ => tiltedLogSineLaw_charFun_six_truncated_continuousOn a b (n : ℝ) ha hab)
  · intro β hβ n m hnm
    apply setIntegral_mono_set
      (tiltedLogSineLaw_charFun_six_integrable (lt_of_lt_of_le ha hβ.1)).integrableOn
      (Eventually.of_forall (fun t => pow_nonneg (norm_nonneg _) _))
    apply Eventually.of_forall
    intro t ht
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    exact ⟨le_trans (neg_le_neg hnm') ht.1, le_trans ht.2 hnm'⟩
  · exact tiltedLogSineLaw_charFun_six_mass_continuousOn a b ha hab
  · intro β hβ
    exact tiltedLogSineLaw_charFun_six_truncated_tendsto (lt_of_lt_of_le ha hβ.1)

/-- Actual sixth-power frequency tails are tight uniformly over compact tilts. -/
theorem tiltedLogSineLaw_charFun_six_uniform_tail
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ β ∈ Icc a b,
      (∫ t in (Icc (-R) R)ᶜ, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp
      (tiltedLogSineLaw_charFun_six_truncated_uniform a b ha hab)) ε hε)
  refine ⟨N, Nat.cast_nonneg N, ?_⟩
  intro β hβ
  have hn := hN N le_rfl β hβ
  rw [setIntegral_compl measurableSet_Icc
    (tiltedLogSineLaw_charFun_six_integrable (lt_of_lt_of_le ha hβ.1))]
  exact lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq] using hn)

#print axioms tiltedDensityTriple_compact_L2_envelope
#print axioms tiltedDensityTriple_parameter_continuousOn
#print axioms tiltedDensityTriple_square_integral_continuousOn
#print axioms tiltedLogSineLaw_charFun_six_mass_continuousOn
#print axioms tiltedLogSineLaw_charFun_six_truncated_continuousOn
#print axioms tiltedLogSineLaw_charFun_six_truncated_tendsto
#print axioms tiltedLogSineLaw_charFun_six_truncated_uniform
#print axioms tiltedLogSineLaw_charFun_six_uniform_tail

end ConditionalSpectralExtremes
