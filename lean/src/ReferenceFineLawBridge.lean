import ReferenceConvolutionDensity
import PathWeightDefinitions
import UniformNoiseSupport

/-! Exact identification with the manuscript's referenceFineLaw, including q=0. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

theorem tiltedLogSineSumLaw_charFun (s : Real) (hs : -1 < s) (q : Nat) (u : Real) :
    charFun ((tiltedLogSineProduct s q).map logSineSum) u = charFun (tiltedLogSineLaw s) u^q := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  have hm : Measurable (@logSineSum q) := by unfold logSineSum; fun_prop
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  unfold logSineSum tiltedLogSineProduct
  push_cast
  simp_rw [Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  rw [charFun_apply_real]
  simpa only [Fintype.card_fin] using! integral_fintype_prod_eq_pow
    (ι := Fin q) (μ := tiltedLogSineLaw s) (fun x : Real => Complex.exp ((u : Complex)*x*Complex.I))

theorem reference_coordinate_eq_logSineSumLaw (s : Real) (hs : -1 < s) (q : Nat) :
    coordinateLaw (referenceVectorSumLaw s 1 q) 0 = (tiltedLogSineProduct s q).map logSineSum := by
  let _ := referenceVectorSumLaw_probability s hs 1 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  let _ := tiltedLogSineProduct_isProbabilityMeasure s q hs
  have hm : Measurable (@logSineSum q) := by unfold logSineSum; fun_prop
  let _ : IsProbabilityMeasure ((tiltedLogSineProduct s q).map logSineSum) := Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_charFun
  ext u
  rw [reference_coordinate_charFun s hs, tiltedLogSineSumLaw_charFun s hs]

theorem tiltedLogSineSumLaw_eq_density (s : Real) (hs : -1 < s) (q : Nat) (hq : 1 ≤ q) :
    (tiltedLogSineProduct s q).map logSineSum =
      volume.withDensity (fun x => ENNReal.ofReal (tiltedDensityPower s q x)) := by
  rw [← reference_coordinate_eq_logSineSumLaw s hs]
  exact reference_coordinate_eq_density s hs q hq

theorem referenceFineLaw_eq_coordinateProduct (s : Real) (hs : -1 < s) (m : Nat) (q : Nat → Nat) :
    referenceFineLaw s m q = Measure.pi (fun i : Fin m => coordinateLaw (referenceVectorSumLaw s 1 (q (i.val+1))) 0) := by
  unfold referenceFineLaw
  congr 1
  funext i
  exact (reference_coordinate_eq_logSineSumLaw s hs (q (i.val+1))).symm

def fineSmoothingNoise (δ : Real) (m : Nat) : Measure (Fin m → Real) :=
  Measure.pi (fun _ : Fin m => tenUniformNoise δ)

theorem fineSmoothingNoise_probability (δ : Real) (hδ : 0 < δ) (m : Nat) :
    IsProbabilityMeasure (fineSmoothingNoise δ m) := by
  let _ := tenUniformNoise_probability δ hδ
  unfold fineSmoothingNoise
  infer_instance

theorem fineSmoothingNoise_support (δ : Real) (hδ : 0 < δ) (m : Nat) :
    ∀ᵐ ζ ∂fineSmoothingNoise δ m, ∀ i : Fin m, |ζ i| ≤ δ := by
  let _ := tenUniformNoise_probability δ hδ
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin m => tenUniformNoise δ) i).quasiMeasurePreserving.tendsto_ae.eventually
    (tenUniformNoise_support δ hδ)

theorem referencePathMass_eq_smoothed_integral (p : FineScales.Parameters) (n : Nat)
    (κ G : Real) (q : Nat → Nat) (noise : Measure (Fin (FineScales.count p n) → Real))
    [IsProbabilityMeasure noise] :
    referencePathMass p n κ G q noise =
      ∫⁻ w, pathWeight p n κ G q w ∂(referenceFineLaw (criticalPoint κ) (FineScales.count p n) q ∗ noise) := by
  rw [Measure.lintegral_conv (pathWeight_measurable p n κ G q)]
  rfl

#print axioms tiltedLogSineSumLaw_eq_density
#print axioms referenceFineLaw_eq_coordinateProduct
#print axioms referencePathMass_eq_smoothed_integral
end ConditionalSpectralAudit.FourierHarmonic
