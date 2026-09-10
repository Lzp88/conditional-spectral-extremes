import CategoricalHistogram
import FiniteChangeMeasure

/-! The actual categorical PMF and the finite positive weighted measure
are exactly the same normalized probability measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralExtremes.BlockCounts
open ConditionalSpectralAudit.FiniteWeighted

theorem categoricalPMF_normalized_measure {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (w : ι → Real) (hw : ∀ i, 0 ≤ w i) (_hW : 0 < ∑ i, w i)
    (hp : ∀ i, 0 ≤ w i/∑ j, w j) (hs : (∑ i, w i/∑ j, w j)=1) :
    (categoricalPMF (fun i => w i/∑ j, w j) hp hs).toMeasure=normalizedLaw Finset.univ w id := by
  classical
  ext A hA
  rw [PMF.toMeasure_apply_fintype,normalizedLaw,Measure.smul_apply,weightedLaw,
    Measure.finsetSum_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [Set.indicator_of_mem hi,categoricalPMF,PMF.ofFintype_apply,Measure.smul_apply,
      id_eq,Measure.dirac_apply_of_mem hi,smul_eq_mul,mul_one]
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (hw i)]
    exact mul_comm _ _
  · simp [Measure.smul_apply,hA,hi]

#print axioms categoricalPMF_normalized_measure
end ConditionalSpectralExtremes.BlockCounts
