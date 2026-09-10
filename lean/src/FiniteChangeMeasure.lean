import FiniteMeasureDensityProduct
import FiniteWeightedLaw

/-! Exact finite reweighting and product-measure identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted

theorem finite_pi_smul {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let _ (i : ι) : IsFiniteMeasure (c i • μ i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top _ _)⟩
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

theorem weightedLaw_withDensity {ι Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (f : Ω → Real) (hw : ∀ i ∈ S, 0 ≤ w i) :
    (weightedLaw S w X).withDensity (fun x => ENNReal.ofReal (f x)) =
      weightedLaw S (fun i => w i * f (X i)) X := by
  classical
  unfold weightedLaw
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, withDensity_add_measure,
        withDensity_smul_measure, dirac_withDensity, smul_smul,
        ← ENNReal.ofReal_mul (hw a (Finset.mem_insert_self _ _))]
      rw [ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))]

theorem weightedLaw_map {ι Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    [MeasurableSingletonClass Ω] (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (f : Ω → Ψ) (hf : Measurable f) :
    (weightedLaw S w X).map f = weightedLaw S w (f ∘ X) := by
  classical
  unfold weightedLaw
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf,
        Measure.map_smul, Measure.map_dirac' hf, ih]
      rfl

theorem normalizedLaw_reweight {ι Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (f : Ω → Real) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ S, w i) (hV : 0 < ∑ i ∈ S, w i * f (X i)) :
    (normalizedLaw S w X).withDensity (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal ((∑ i ∈ S, w i*f (X i))/(∑ i ∈ S, w i)) •
        normalizedLaw S (fun i => w i*f (X i)) X := by
  rw [normalizedLaw, withDensity_smul_measure, weightedLaw_withDensity S w X f hw,
    normalizedLaw, smul_smul, ← ENNReal.ofReal_mul (div_nonneg hV.le hW.le)]
  congr 1
  congr 1
  field_simp

#print axioms finite_pi_smul
#print axioms normalizedLaw_reweight
end ConditionalSpectralAudit.FourierHarmonic
