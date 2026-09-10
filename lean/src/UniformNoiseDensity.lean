import UniformSmoothingNoise
import TiltedDensityPowerRegularity
import TiltedCharacteristicL6

/-! Actual convolution densities for the prescribed uniform smoothing law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Real Complex ENNReal Convolution

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def uniformDensity (h : Real) : Real → Real := (Ioc (-h) h).indicator (fun _ => (2 * h)⁻¹)

theorem uniformDensity_measurable (h : Real) : Measurable (uniformDensity h) :=
  measurable_const.indicator measurableSet_Ioc

theorem uniformDensity_nonneg (h : Real) (hh : 0 < h) (x : Real) : 0 ≤ uniformDensity h x := by
  unfold uniformDensity
  exact indicator_nonneg (fun _ _ => by positivity) x

theorem uniformDensity_bound (h : Real) (hh : 0 < h) (x : Real) :
    ‖uniformDensity h x‖ ≤ (2 * h)⁻¹ := by
  unfold uniformDensity
  by_cases hx : x ∈ Ioc (-h) h
  · rw [indicator_of_mem hx, Real.norm_of_nonneg (by positivity)]
  · rw [indicator_of_notMem hx, norm_zero]
    positivity

theorem uniformDensity_memLp (h : Real) (p : ENNReal) : MemLp (uniformDensity h) p volume := by
  exact memLp_indicator_const p measurableSet_Ioc _ (Or.inr (by simp))

theorem uniformDensity_integrable (h : Real) : Integrable (uniformDensity h) :=
  memLp_one_iff_integrable.mp (uniformDensity_memLp h 1)

theorem uniformDensity_integral (h : Real) (hh : 0 < h) : (∫ x, uniformDensity h x) = 1 := by
  rw [uniformDensity, integral_indicator measurableSet_Ioc, integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ h - -h)]
  rw [show h - -h = 2 * h by ring]
  exact mul_inv_cancel₀ (by positivity : (2 * h : Real) ≠ 0)

theorem symmetricUniform_eq_density (h : Real) :
    symmetricUniform h = volume.withDensity (fun x => ENNReal.ofReal (uniformDensity h x)) := by
  have he : (fun x => ENNReal.ofReal (uniformDensity h x)) =
      (Ioc (-h) h).indicator (fun _ => ENNReal.ofReal ((2 * h)⁻¹)) := by
    ext x
    by_cases hx : x ∈ Ioc (-h) h <;> simp [uniformDensity, hx]
  rw [he, withDensity_indicator measurableSet_Ioc, withDensity_const]
  rfl

/-- Index q represents q+1 actual uniform summands. -/
def uniformDensityPower (h : Real) : Nat → Real → Real
  | 0 => uniformDensity h
  | q + 1 => uniformDensityPower h q ⋆[ContinuousLinearMap.mul Real Real] uniformDensity h

theorem uniformDensityPower_integrable (h : Real) (q : Nat) : Integrable (uniformDensityPower h q) := by
  induction q with
  | zero => exact uniformDensity_integrable h
  | succ q ih => exact ih.integrable_convolution (L := ContinuousLinearMap.mul Real Real) (uniformDensity_integrable h)

theorem uniformDensityPower_nonneg (h : Real) (hh : 0 < h) (q : Nat) (x : Real) :
    0 ≤ uniformDensityPower h q x := by
  induction q generalizing x with
  | zero => exact uniformDensity_nonneg h hh x
  | succ q ih =>
    change 0 ≤ ∫ y, uniformDensityPower h q y * uniformDensity h (x-y)
    exact integral_nonneg (fun y => mul_nonneg (ih y) (uniformDensity_nonneg h hh (x-y)))

theorem uniformDensityPower_integral (h : Real) (hh : 0 < h) (q : Nat) :
    (∫ x, uniformDensityPower h q x) = 1 := by
  induction q with
  | zero => exact uniformDensity_integral h hh
  | succ q ih =>
    change (∫ x, (uniformDensityPower h q ⋆[ContinuousLinearMap.mul Real Real] uniformDensity h) x) = 1
    rw [integral_convolution _ (uniformDensityPower_integrable h q) (uniformDensity_integrable h),
      ih, uniformDensity_integral h hh]
    simp

theorem uniformDensityPower_bound (h : Real) (hh : 0 < h) (q : Nat) (x : Real) :
    ‖uniformDensityPower h q x‖ ≤ (2 * h)⁻¹ := by
  induction q generalizing x with
  | zero => exact uniformDensity_bound h hh x
  | succ q ih =>
    exact convolution_bound_of_probability_right (uniformDensityPower_integrable h q).1 ih
      (uniformDensity_integrable h) (uniformDensity_nonneg h hh) (uniformDensity_integral h hh) x

theorem uniformDensityPower_continuous (h : Real) (hh : 0 < h) (q : Nat) (hq : 1 ≤ q) :
    Continuous (uniformDensityPower h q) := by
  induction q, hq using Nat.le_induction with
  | base =>
    exact convolution_continuous_of_memLp (p := 2) (q := 2) (by norm_num)
      (uniformDensity_memLp h 2) (uniformDensity_memLp h 2)
  | succ q hq ih =>
    have hb : BddAbove (range (fun x => ‖uniformDensityPower h q x‖)) :=
      ⟨(2*h)⁻¹, by rintro _ ⟨x, rfl⟩; exact uniformDensityPower_bound h hh q x⟩
    exact hb.continuous_convolution_left_of_integrable _ ih (uniformDensity_integrable h)

theorem probability_of_real_density {f : Real → Real} (hf : Integrable f)
    (hn : ∀ x, 0 ≤ f x) (h1 : ∫ x, f x = 1) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn), h1]
  norm_num

theorem uniformDensityPower_charFun (h : Real) (hh : 0 < h) (q : Nat) (u : Real) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (uniformDensityPower h q x))) u =
      charFun (symmetricUniform h) u ^ (q+1) := by
  induction q with
  | zero => simp [uniformDensityPower, ← symmetricUniform_eq_density]
  | succ q ih =>
    let _ := probability_of_real_density (uniformDensityPower_integrable h q)
      (uniformDensityPower_nonneg h hh q) (uniformDensityPower_integral h hh q)
    let _ := probability_of_real_density (uniformDensity_integrable h)
      (uniformDensity_nonneg h hh) (uniformDensity_integral h hh)
    change charFun (volume.withDensity (fun x => ENNReal.ofReal
      ((uniformDensityPower h q ⋆[ContinuousLinearMap.mul Real Real] uniformDensity h) x))) u = _
    rw [← real_density_convolution (uniformDensityPower_integrable h q) (uniformDensity_integrable h)
      (uniformDensityPower_nonneg h hh q) (uniformDensity_nonneg h hh), charFun_conv, ih,
      ← symmetricUniform_eq_density]
    simp only [pow_succ]

theorem tenUniformNoise_eq_density (δ : Real) (hδ : 0 < δ) :
    tenUniformNoise δ = volume.withDensity (fun x => ENNReal.ofReal (uniformDensityPower (δ/10) 9 x)) := by
  let _ := tenUniformNoise_probability δ hδ
  let _ := probability_of_real_density (uniformDensityPower_integrable (δ/10) 9)
    (uniformDensityPower_nonneg (δ/10) (by positivity) 9)
    (uniformDensityPower_integral (δ/10) (by positivity) 9)
  apply Measure.ext_of_charFun
  ext u
  rw [tenUniformNoise_charFun δ u hδ, uniformDensityPower_charFun (δ/10) (by positivity) 9 u]

#print axioms uniformDensityPower_continuous
#print axioms tenUniformNoise_eq_density
end ConditionalSpectralAudit.FourierHarmonic
