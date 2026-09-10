import PoissonMultinomialCoupling

/-! A probability transfer inequality for events in the actual common
Poisson–multinomial coupling. Both marginal measures are exact. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem poissonMultinomialCoupling_event_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ)
    (A B : (ι → ℕ) → Prop) (D : CoupledCounts ι → Prop)
    (hAB : ∀ z : CoupledCounts ι, CountsCoupled z → A z.2.1 → B z.1 ∨ D z) :
    (naturalMultinomialPMF p hp hpsum k).toMeasure.real {Y | A Y} ≤
      (independentPoissonCountLaw ⟨(k : ℝ), Nat.cast_nonneg k⟩ p hp).real {X | B X}+
        (poissonMultinomialCoupling p hp hpsum k).toMeasure.real {z | D z} := by
  let Q := poissonMultinomialCoupling p hp hpsum k
  have hY : Q.toMeasure.real {z | A z.2.1} =
      (naturalMultinomialPMF p hp hpsum k).toMeasure.real {Y | A Y} := by
    rw [← poissonMultinomialCoupling_second_measure p hp hpsum k]
    simp only [measureReal_def]
    rw [Measure.map_apply (Measurable.of_discrete : Measurable (fun z : CoupledCounts ι => z.2.1))
      (MeasurableSet.of_discrete : MeasurableSet {Y | A Y})]
    rfl
  have hX : Q.toMeasure.real {z | B z.1} =
      (independentPoissonCountLaw ⟨(k : ℝ), Nat.cast_nonneg k⟩ p hp).real {X | B X} := by
    rw [← poissonMultinomialCoupling_first_measure p hp hpsum k]
    simp only [measureReal_def]
    rw [Measure.map_apply measurable_fst (MeasurableSet.of_discrete : MeasurableSet {X | B X})]
    rfl
  rw [← hY, ← hX]
  have hsub : {z : CoupledCounts ι | A z.2.1} ∩ Q.support ⊆
      {z | B z.1} ∪ {z | D z} := by
    intro z hz
    exact hAB z (poissonMultinomialCoupling_support p hp hpsum k z hz.2) hz.1
  have hm := Q.toMeasure_mono (MeasurableSet.of_discrete : MeasurableSet {z : CoupledCounts ι | A z.2.1}) hsub
  have hh : Q.toMeasure.real {z | A z.2.1} ≤ Q.toMeasure.real ({z | B z.1} ∪ {z | D z}) :=
    ENNReal.toReal_mono (measure_ne_top _ _) hm
  exact hh.trans (measureReal_union_le _ _)

#print axioms poissonMultinomialCoupling_event_bound

end ConditionalSpectralExtremes.BlockCounts
