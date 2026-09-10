import FiniteMeasureDensityProduct

/-! Independent product noise is the convolution of the actual path laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem finite_pi_convolution {ι α : Type*} [Fintype ι] [AddMonoid α]
    [MeasurableSpace α] [MeasurableAdd₂ α]
    (μ ν : ι → Measure α) [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    (Measure.pi μ) ∗ (Measure.pi ν) = Measure.pi (fun i => μ i ∗ ν i) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow α α ι μ ν
  rw [Measure.conv, ← hmp.map_eq, Measure.map_map measurable_add hmp.measurable]
  change (Measure.pi (fun i => (μ i).prod (ν i))).map
      (fun x i => (x i).1+(x i).2) = _
  rw [Measure.pi_map_pi (fun _ => measurable_add.aemeasurable)]
  rfl

#print axioms finite_pi_convolution
end ConditionalSpectralAudit.FourierHarmonic
