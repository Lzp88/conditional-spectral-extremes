import PairSmoothedFourier
import PairBox

/-! Event total variation for the genuine two-dimensional smoothed measures. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

def pairTotalVariationDistance (μ ν : Measure PairSpace) : Real :=
  ⨆ A : {A : Set PairSpace // MeasurableSet A}, |μ.real A - ν.real A|

theorem pairRealDensity_event (f : PairSpace → Real) (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (A : Set PairSpace) (hA : MeasurableSet A) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).real A = ∫ x in A, f x := by
  rw [measureReal_def, withDensity_apply _ hA]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hn) hf.integrableOn.1).symm

theorem pairRealDensity_event_difference (f g : PairSpace → Real) (hf : Integrable f) (hg : Integrable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (A : Set PairSpace) (hA : MeasurableSet A) :
    |(volume.withDensity (fun x => ENNReal.ofReal (f x))).real A -
      (volume.withDensity (fun x => ENNReal.ofReal (g x))).real A| ≤ ∫ x, |f x-g x| := by
  rw [pairRealDensity_event f hf hfn A hA, pairRealDensity_event g hg hgn A hA,
    ← integral_sub hf.integrableOn hg.integrableOn]
  have hh := norm_integral_le_integral_norm (fun x => f x-g x) (μ := volume.restrict A)
  simp only [Real.norm_eq_abs] at hh
  apply hh.trans
  exact setIntegral_le_integral (hf.sub hg).abs (ae_of_all _ (fun x => abs_nonneg _))

theorem pairSmoothedDensity_l1_box_bound (δ K C : Real) (hδ : 0 < δ) (hK : 0 ≤ K)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hC : ∀ x, |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x| ≤ C) :
    (∫ x, |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x|) ≤
      4*K^2*C + (μ ∗ pairUniformNoise δ).real (pairBox K)ᶜ +
        (ν ∗ pairUniformNoise δ).real (pairBox K)ᶜ := by
  let _ : IsFiniteMeasure (volume.restrict (pairBox K)) := ⟨by
    rw [Measure.restrict_apply_univ, pairBox_volume]
    finiteness⟩
  have hf := pairSmoothedDensity_integrable δ μ
  have hg := pairSmoothedDensity_integrable δ ν
  have hi : Integrable (fun x => |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x|) := (hf.sub hg).abs
  have hcore : (∫ x in pairBox K, |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x|) ≤ 4*K^2*C := by
    calc
      _ ≤ ∫ x in pairBox K, C := integral_mono hi.integrableOn (integrable_const C) hC
      _ = _ := by
        rw [integral_const]
        simpa only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] using
          congrArg (fun a : Real => a*C) (pairBox_volume_real K hK)
  have htail : (∫ x in (pairBox K)ᶜ, |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x|) ≤
      (μ ∗ pairUniformNoise δ).real (pairBox K)ᶜ +
        (ν ∗ pairUniformNoise δ).real (pairBox K)ᶜ := by
    calc
      _ ≤ ∫ x in (pairBox K)ᶜ, pairSmoothedDensity δ μ x+pairSmoothedDensity δ ν x := by
        apply integral_mono hi.integrableOn (hf.add hg).integrableOn
        intro x
        simp only [Pi.add_apply]
        apply abs_le.mpr
        constructor <;> linarith [pairSmoothedDensity_nonneg δ hδ μ x, pairSmoothedDensity_nonneg δ hδ ν x]
      _ = _ := by
        rw [integral_add hf.integrableOn hg.integrableOn,
          pairSmoothing_eq_density δ hδ μ, pairSmoothing_eq_density δ hδ ν,
          pairRealDensity_event _ hf (pairSmoothedDensity_nonneg δ hδ μ) _ (measurableSet_pairBox K).compl,
          pairRealDensity_event _ hg (pairSmoothedDensity_nonneg δ hδ ν) _ (measurableSet_pairBox K).compl]
  rw [← integral_add_compl (measurableSet_pairBox K) hi]
  linarith

theorem pairSmoothing_totalVariation_box_bound (δ K C : Real) (hδ : 0 < δ) (hK : 0 ≤ K)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hC : ∀ x, |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x| ≤ C) :
    pairTotalVariationDistance (μ ∗ pairUniformNoise δ) (ν ∗ pairUniformNoise δ) ≤
      4*K^2*C + (μ ∗ pairUniformNoise δ).real (pairBox K)ᶜ +
        (ν ∗ pairUniformNoise δ).real (pairBox K)ᶜ := by
  let _ : Nonempty {A : Set PairSpace // MeasurableSet A} := ⟨⟨univ, MeasurableSet.univ⟩⟩
  apply ciSup_le
  intro A
  have hh := pairRealDensity_event_difference (pairSmoothedDensity δ μ) (pairSmoothedDensity δ ν)
    (pairSmoothedDensity_integrable δ μ) (pairSmoothedDensity_integrable δ ν)
    (pairSmoothedDensity_nonneg δ hδ μ) (pairSmoothedDensity_nonneg δ hδ ν) A A.2
  rw [← pairSmoothing_eq_density δ hδ μ, ← pairSmoothing_eq_density δ hδ ν] at hh
  exact hh.trans (pairSmoothedDensity_l1_box_bound δ K C hδ hK μ ν hC)

#print axioms pairSmoothing_totalVariation_box_bound
end ConditionalSpectralAudit.FourierHarmonic
