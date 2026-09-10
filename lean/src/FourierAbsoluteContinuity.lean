import FourierDerivativeFoundation

/-! Absolute continuity of the actual periodic complex power.  The
Banach-valued primitive lemma below extends mathlib's real-valued lemma
using the same absolute-integrability argument and the norm inequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter Function
open scoped Topology BigOperators
namespace ConditionalSpectralAudit.FourierDerivative

theorem intervalIntegral_absolutelyContinuous {F : Type*}
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real → F} {a b c : Real} (h : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b := by
  open AbsolutelyContinuousOnInterval in
  let s := fun E : Nat × (Nat → Real × Real) =>
    ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  open AbsolutelyContinuousOnInterval in
  have ht : Tendsto (fun i => ∫⁻ x in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hr := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp ht
  refine squeeze_zero' ?_ ?_ hr
  · filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  open AbsolutelyContinuousOnInterval in
  have he : ∀ᶠ E : Nat × (Nat → Real × Real) in
      totalLengthFilter ⊓ 𝓟 (disjWithin a b), E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [he] with E hE
  obtain ⟨hE1,hE2⟩ := mem_ofPred_eq ▸ hE
  dsimp only [Function.comp_apply,s]
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hE2]
  · apply Finset.sum_le_sum
    intro i hi
    have hsub := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
      hE (Finset.mem_range.mp hi)
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc,uIcc])
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc,uIcc]),
      Measure.restrict_restrict_of_subset hsub]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc
        (f := f) (μ := volume) (a := (E.2 i).2) (b := (E.2 i).1))
  · intro i hi
    unfold IntegrableOn
    have hsub := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
      hE (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsub]
    exact IntegrableOn.mono_set h.def'.norm hsub |>.integrable

theorem absolutelyContinuous_congrOn {F : Type*} [PseudoMetricSpace F]
    {f g : Real → F} {a b : Real}
    (hf : AbsolutelyContinuousOnInterval f a b) (he : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  apply hf.congr'
  open AbsolutelyContinuousOnInterval in
  have hm : ∀ᶠ E : Nat × (Nat → Real × Real) in
      totalLengthFilter ⊓ 𝓟 (disjWithin a b), E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hm] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [he (hE.1 i hi).1,he (hE.1 i hi).2]

theorem circlePhiLift_zero (z : Complex) (hz : 0 < z.re) : circlePhiLift z 0=0 := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  simp [circlePhiLift,FourierTail.complexPhi,hn]

theorem circlePhiDerivative_primitive (z : Complex) (hz : 0 < z.re)
    {x : Real} (hx : x ∈ Icc (0 : Real) 1) :
    (∫ t in (0 : Real)..x, circlePhiDerivative z t)=circlePhiLift z x := by
  have hint := (circlePhiDerivative_intervalIntegrable z hz).mono_set
    (show uIcc (0 : Real) x ⊆ uIcc (0 : Real) 1 by
      rw [uIcc_of_le hx.1,uIcc_of_le (by norm_num : (0:Real)≤1)]
      exact Icc_subset_Icc le_rfl hx.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (circlePhiLift_continuous z hz).continuousOn
    (fun t ht => (circlePhiLift_hasDerivAt z hz
      (show t ∈ Ioo (0:Real) 1 from ⟨ht.1,ht.2.trans_le hx.2⟩)).differentiableAt.hasDerivAt)
    hint
  simpa only [circlePhiDerivative,circlePhiLift_zero z hz,sub_zero] using h

theorem circlePhiLift_absolutelyContinuous (z : Complex) (hz : 0 < z.re) :
    AbsolutelyContinuousOnInterval (circlePhiLift z) 0 1 := by
  apply absolutelyContinuous_congrOn
    (intervalIntegral_absolutelyContinuous (circlePhiDerivative_intervalIntegrable z hz)
      (c := 0) (by simp))
  intro x hx
  rw [uIcc_of_le (by norm_num : (0:Real)≤1)] at hx
  exact circlePhiDerivative_primitive z hz hx

#print axioms intervalIntegral_absolutelyContinuous
#print axioms circlePhiDerivative_primitive
#print axioms circlePhiLift_absolutelyContinuous
end ConditionalSpectralAudit.FourierDerivative
