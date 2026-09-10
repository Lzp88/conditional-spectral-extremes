import Mathlib

/-! A genuine finite weighted probability measure, allowing zero weights. -/
noncomputable section
open MeasureTheory Set

namespace ConditionalSpectralAudit.FiniteWeighted

variable {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def weightedLaw (S : Finset ι) (w : ι → Real) (X : ι → Ω) : Measure Ω :=
  ∑ i ∈ S, ENNReal.ofReal (w i) • Measure.dirac (X i)

def normalizedLaw (S : Finset ι) (w : ι → Real) (X : ι → Ω) : Measure Ω :=
  ENNReal.ofReal ((∑ i ∈ S, w i)⁻¹) • weightedLaw S w X

omit [MeasurableSingletonClass Ω] in
theorem weightedLaw_univ (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    weightedLaw S w X univ = ENNReal.ofReal (∑ i ∈ S, w i) := by
  simp only [weightedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg hw).symm

omit [MeasurableSingletonClass Ω] in
theorem normalizedLaw_isProbabilityMeasure (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hW : 0 < ∑ i ∈ S, w i) :
    IsProbabilityMeasure (normalizedLaw S w X) := by
  constructor
  rw [normalizedLaw, Measure.smul_apply, weightedLaw_univ S w X hw]
  simp only [smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hW.le),
    inv_mul_cancel₀ hW.ne', ENNReal.ofReal_one]

theorem weightedLaw_integrable (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (f : Ω → Complex) : Integrable f (weightedLaw S w X) := by
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem weightedLaw_integral (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (hw : ∀ i ∈ S, 0 ≤ w i) (f : Ω → Complex) :
    (∫ x, f x ∂weightedLaw S w X) = ∑ i ∈ S, (w i : Complex) * f (X i) := by
  unfold weightedLaw
  rw [integral_finsetSum_measure (fun i hi =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i hi)]
  rfl

theorem normalizedLaw_integral (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (hw : ∀ i ∈ S, 0 ≤ w i) (f : Ω → Complex) :
    (∫ x, f x ∂normalizedLaw S w X) =
      (∑ i ∈ S, (w i : Complex) * f (X i)) / ((∑ i ∈ S, w i : Real) : Complex) := by
  rw [normalizedLaw, integral_smul_measure, weightedLaw_integral S w X hw,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Finset.sum_nonneg hw))]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  ring

omit [MeasurableSingletonClass Ω] in
theorem zero_weight_irrelevant (S : Finset ι) (w : ι → Real) (X Y : ι → Ω)
    (he : ∀ i ∈ S, w i ≠ 0 → X i = Y i) : weightedLaw S w X = weightedLaw S w Y := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : w i = 0
  · simp [hz]
  · rw [he i hi hz]

#print axioms normalizedLaw_isProbabilityMeasure
#print axioms normalizedLaw_integral
end ConditionalSpectralAudit.FiniteWeighted
