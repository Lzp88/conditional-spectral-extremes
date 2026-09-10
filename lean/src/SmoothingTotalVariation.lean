import ProbabilitySmoothingDensity

/-! Total variation is the supremum of event probability discrepancies.
The proof controls genuine smoothed measures by their actual densities and tails. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic

def totalVariationDistance (μ ν : Measure Real) : Real :=
  ⨆ A : {A : Set Real // MeasurableSet A}, |μ.real A - ν.real A|

theorem realDensity_event (f : Real → Real) (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (A : Set Real) (hA : MeasurableSet A) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).real A = ∫ x in A, f x := by
  rw [measureReal_def, withDensity_apply _ hA]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hn) hf.integrableOn.1).symm

theorem realDensity_event_difference (f g : Real → Real) (hf : Integrable f) (hg : Integrable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (A : Set Real) (hA : MeasurableSet A) :
    |(volume.withDensity (fun x => ENNReal.ofReal (f x))).real A -
      (volume.withDensity (fun x => ENNReal.ofReal (g x))).real A| ≤ ∫ x, |f x-g x| := by
  rw [realDensity_event f hf hfn A hA, realDensity_event g hg hgn A hA,
    ← integral_sub hf.integrableOn hg.integrableOn]
  have hh := norm_integral_le_integral_norm (fun x => f x-g x) (μ := volume.restrict A)
  simp only [Real.norm_eq_abs] at hh
  apply hh.trans
  exact setIntegral_le_integral (hf.sub hg).abs (ae_of_all _ (fun x => abs_nonneg _))

theorem smoothedDensity_l1_box_bound (δ K C : Real) (hδ : 0 < δ) (hK : 0 ≤ K)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hC : ∀ x, |smoothedDensity δ μ x-smoothedDensity δ ν x| ≤ C) :
    (∫ x, |smoothedDensity δ μ x-smoothedDensity δ ν x|) ≤
      2*K*C + (μ ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ +
        (ν ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ := by
  have hf := smoothedDensity_integrable δ μ
  have hg := smoothedDensity_integrable δ ν
  have hi : Integrable (fun x => |smoothedDensity δ μ x-smoothedDensity δ ν x|) := (hf.sub hg).abs
  have hcore : (∫ x in Icc (-K) K, |smoothedDensity δ μ x-smoothedDensity δ ν x|) ≤ 2*K*C := by
    calc
      _ ≤ ∫ x in Icc (-K) K, C := integral_mono hi.integrableOn (integrable_const C) hC
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ K - -K)]
        simp only [smul_eq_mul]
        ring
  have htail : (∫ x in (Icc (-K) K)ᶜ, |smoothedDensity δ μ x-smoothedDensity δ ν x|) ≤
      (μ ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ +
        (ν ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ := by
    calc
      _ ≤ ∫ x in (Icc (-K) K)ᶜ, smoothedDensity δ μ x+smoothedDensity δ ν x := by
        apply integral_mono hi.integrableOn (hf.add hg).integrableOn
        intro x
        simp only [Pi.add_apply]
        apply abs_le.mpr
        constructor <;> linarith [smoothedDensity_nonneg δ hδ μ x, smoothedDensity_nonneg δ hδ ν x]
      _ = _ := by
        rw [integral_add hf.integrableOn hg.integrableOn,
          smoothing_eq_density δ hδ μ, smoothing_eq_density δ hδ ν,
          realDensity_event _ hf (smoothedDensity_nonneg δ hδ μ) _ measurableSet_Icc.compl,
          realDensity_event _ hg (smoothedDensity_nonneg δ hδ ν) _ measurableSet_Icc.compl]
  rw [← integral_add_compl measurableSet_Icc hi]
  linarith

theorem smoothing_totalVariation_box_bound (δ K C : Real) (hδ : 0 < δ) (hK : 0 ≤ K)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hC : ∀ x, |smoothedDensity δ μ x-smoothedDensity δ ν x| ≤ C) :
    totalVariationDistance (μ ∗ tenUniformNoise δ) (ν ∗ tenUniformNoise δ) ≤
      2*K*C + (μ ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ +
        (ν ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ := by
  let _ : Nonempty {A : Set Real // MeasurableSet A} := ⟨⟨univ, MeasurableSet.univ⟩⟩
  apply ciSup_le
  intro A
  have hh := realDensity_event_difference (smoothedDensity δ μ) (smoothedDensity δ ν)
    (smoothedDensity_integrable δ μ) (smoothedDensity_integrable δ ν)
    (smoothedDensity_nonneg δ hδ μ) (smoothedDensity_nonneg δ hδ ν) A A.2
  rw [← smoothing_eq_density δ hδ μ, ← smoothing_eq_density δ hδ ν] at hh
  exact hh.trans (smoothedDensity_l1_box_bound δ K C hδ hK μ ν hC)

#print axioms smoothing_totalVariation_box_bound
end ConditionalSpectralAudit.FourierHarmonic
