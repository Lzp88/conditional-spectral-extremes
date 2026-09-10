import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! A quantitative probability-error bound for bounded Lipschitz tests. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes

theorem bounded_lipschitz_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (F : E → Real) (M : Real) (hF : Continuous F) (hM : ∀ x y, dist (F x) (F y)≤M) :
    Integrable (fun x => F (X x)) μ := by
  apply Integrable.of_bound (hF.measurable.comp hX).aestronglyMeasurable (‖F 0‖+M)
  apply ae_of_all
  intro x
  have hh := hM (X x) 0
  rw [Real.dist_eq] at hh
  calc
    ‖F (X x)‖ = ‖F (X x)-F 0+F 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖F (X x)-F 0‖+‖F 0‖ := norm_add_le _ _
    _ ≤ M+‖F 0‖ := by simpa only [Real.norm_eq_abs] using add_le_add hh (le_refl ‖F 0‖)
    _ = _ := by ring

theorem bounded_lipschitz_integral_error {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (F : E → Real) (M : Real) (L : NNReal) (hM : ∀ x y, dist (F x) (F y)≤M)
    (hLip : LipschitzWith L F) (ε : Real) (hε : 0 ≤ ε) :
    |(∫ ω, F (Y ω) ∂μ)-(∫ ω, F (X ω) ∂μ)|≤
      L*ε+M*μ.real {ω | ε≤‖Y ω-X ω‖} := by
  let S : Set Ω := {ω | ε≤‖Y ω-X ω‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const (hY.sub hX).norm
  have hFX := bounded_lipschitz_integrable μ X hX F M hLip.continuous hM
  have hFY := bounded_lipschitz_integrable μ Y hY F M hLip.continuous hM
  have hI : Integrable (fun ω => (L : Real)*ε+S.indicator (fun _ => M) ω) μ :=
    (integrable_const _).add ((integrable_const M).indicator hS)
  have hp (ω : Ω) : ‖F (Y ω)-F (X ω)‖≤(L : Real)*ε+S.indicator (fun _ => M) ω := by
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω]
      have hh := hM (Y ω) (X ω)
      rw [dist_eq_norm] at hh
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg L.coe_nonneg hε))
    · rw [indicator_of_notMem hω,add_zero]
      have hd : ‖Y ω-X ω‖≤ε := (lt_of_not_ge hω).le
      exact hLip.norm_sub_le_of_le hd
  rw [← integral_sub hFY hFX,← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ ω, ‖F (Y ω)-F (X ω)‖ ∂μ) ≤ ∫ ω, (L : Real)*ε+S.indicator (fun _ => M) ω ∂μ :=
      integral_mono_ae (hFY.sub hFX).norm hI (ae_of_all _ hp)
    _ = _ := by
      rw [integral_add (integrable_const _) ((integrable_const M).indicator hS),integral_indicator hS]
      simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
        univ_inter,smul_eq_mul]
      have hμ : μ.real univ = 1 := by simp [measureReal_def]
      rw [hμ]
      ring

#print axioms bounded_lipschitz_integral_error
end ConditionalSpectralExtremes
