import ReferenceCoordinateIndependence
import TiltedDensityPowerFourier
import UniformNoiseDensity

/-! Identification of the actual one-coordinate reference law with f_s^{*q}, for every q ≥ 1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped FourierTransform

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem tiltedDensityPower_measurable (s : Real) (q : Nat) : Measurable (tiltedDensityPower s q) := by
  induction q using Nat.twoStepInduction with
  | zero => exact measurable_const
  | one => exact tiltedDensity_measurable s
  | more n _ ih =>
    change Measurable (fun x => ∫ y, tiltedDensityPower s (n+1) y * tiltedDensity s (x-y))
    have hh : Measurable (fun p : Real × Real => tiltedDensityPower s (n+1) p.2 * tiltedDensity s (p.1-p.2)) :=
      (ih.comp measurable_snd).mul ((tiltedDensity_measurable s).comp (measurable_fst.sub measurable_snd))
    exact hh.stronglyMeasurable.integral_prod_right'.measurable

theorem reference_coordinate_charFun (s : Real) (hs : -1 < s) (q : Nat) (u : Real) :
    charFun (coordinateLaw (referenceVectorSumLaw s 1 q) 0) u = charFun (tiltedLogSineLaw s) u^q := by
  rw [coordinateLaw_charFun_one, referenceVectorSumLaw_transform s hs]
  simp only [Fin.prod_univ_one, pow_one, tiltedLogSineLaw_charFun_eq_Gamma s u hs]

theorem reference_coordinate_eq_density (s : Real) (hs : -1 < s) (q : Nat) (hq : 1 ≤ q) :
    coordinateLaw (referenceVectorSumLaw s 1 q) 0 =
      volume.withDensity (fun x => ENNReal.ofReal (tiltedDensityPower s q x)) := by
  let _ := referenceVectorSumLaw_probability s hs 1 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  let _ := probability_of_real_density
    (tiltedDensityPower_integrable hs q) (tiltedDensityPower_nonneg s q)
    (tiltedDensityPower_integral hs q hq)
  apply Measure.ext_of_charFun
  ext u
  rw [reference_coordinate_charFun s hs,
    charFun_real_density_fourier _ (tiltedDensityPower_measurable s q) (tiltedDensityPower_nonneg s q),
    tiltedDensityPower_fourier hs q hq]
  have harg : -2*Real.pi*(-u/(2*Real.pi))=u := by field_simp
  rw [harg]

#print axioms reference_coordinate_eq_density
end ConditionalSpectralAudit.FourierHarmonic
