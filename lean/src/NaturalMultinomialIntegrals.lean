import NaturalMultinomialLaw

/-! The actual natural-vector multinomial measure integrates by the finite
mass sum, including integrability of every real function on its finite support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem naturalMultinomial_integrable (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (f : (ι → ℕ) → ℝ) :
    Integrable f (naturalMultinomialPMF p hp hpsum k).toMeasure := by
  let : MeasurableSpace (countFiber ι k k) := ⊤
  have hv : Measurable (naturalCountVector : countFiber ι k k → ι → ℕ) := .of_discrete
  rw [naturalMultinomialPMF, ← PMF.toMeasure_map _ _ hv]
  exact (integrable_map_measure (.of_discrete : AEStronglyMeasurable f _)
    hv.aemeasurable).mpr .of_finite

theorem naturalMultinomial_integral (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (f : (ι → ℕ) → ℝ) :
    (∫ c, f c ∂(naturalMultinomialPMF p hp hpsum k).toMeasure) =
      ∑ c : countFiber ι k k, multinomialMass p k c*f (naturalCountVector c) := by
  let : MeasurableSpace (countFiber ι k k) := ⊤
  have hv : Measurable (naturalCountVector : countFiber ι k k → ι → ℕ) := .of_discrete
  rw [naturalMultinomialPMF, ← PMF.toMeasure_map _ _ hv,
    integral_map hv.aemeasurable
      (.of_discrete : AEStronglyMeasurable f _), PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [multinomialPMF_apply, ENNReal.toReal_ofReal (multinomialMass_nonneg hp k c)]
  rfl

#print axioms naturalMultinomial_integrable
#print axioms naturalMultinomial_integral

end ConditionalSpectralExtremes.BlockCounts
