import NaturalMultinomialIntegrals

/-! Exact event probabilities for the natural count-vector multinomial law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem naturalMultinomial_probability (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (A : (ι → ℕ) → Prop) :
    (naturalMultinomialPMF p hp hpsum k).toMeasure.real {Y | A Y} =
      multinomialProbability p k (fun c => A (naturalCountVector c)) := by
  have hh := naturalMultinomial_integral p hp hpsum k ({Y | A Y}.indicator (1 : (ι → ℕ) → ℝ))
  rw [integral_indicator_one (MeasurableSet.of_discrete : MeasurableSet {Y | A Y})] at hh
  simpa only [multinomialProbability, Set.indicator_apply, mem_ofPred_eq, Pi.one_apply,
    mul_ite, mul_one, mul_zero] using hh

#print axioms naturalMultinomial_probability

end ConditionalSpectralExtremes.BlockCounts
