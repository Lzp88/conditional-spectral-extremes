import ProductDensityL1
import BoundedDensityWeight

/-! The linear tensor error applies to every actual bounded path weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem finite_product_weight_difference {n : Nat} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin n) → Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f g : (i : Fin n) → α i → Real)
    (hf : ∀ i, Integrable (f i) (μ i)) (hg : ∀ i, Integrable (g i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hf1 : ∀ i, ∫ x, f i x ∂μ i = 1) (hg1 : ∀ i, ∫ x, g i x ∂μ i = 1)
    (w : ((i : Fin n) → α i) → ENNReal) (hw : Measurable w) (hw1 : ∀ x, w x ≤ 1) :
    |(∫⁻ x, w x ∂Measure.pi (fun i => (μ i).withDensity (fun z => ENNReal.ofReal (f i z)))).toReal-
      (∫⁻ x, w x ∂Measure.pi (fun i => (μ i).withDensity (fun z => ENNReal.ofReal (g i z)))).toReal| ≤
      ∑ i, ∫ x, |f i x-g i x| ∂μ i := by
  rw [finite_measure_density_product μ f hf hf0, finite_measure_density_product μ g hg hg0]
  apply (real_density_weight_difference (Measure.pi μ) _ _
    (Integrable.fintype_prod_dep hf) (Integrable.fintype_prod_dep hg)
    (fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i)))
    (fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))) w hw hw1).trans
  exact finite_product_density_l1 μ f g hf hg hf0 hg0 hf1 hg1

#print axioms finite_product_weight_difference
end ConditionalSpectralAudit.FourierHarmonic
