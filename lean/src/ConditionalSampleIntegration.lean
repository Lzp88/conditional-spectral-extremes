import HarmonicSamplingSupport
import Mathlib.MeasureTheory.Measure.Prod

/-! Exact integration over an independent low sample. The event may
depend arbitrarily on that sample, including through a random angular set. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ConditionalSpectralExtremes

theorem independent_countable_event_bound {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSingletonClass Ω₁] [MeasurableSingletonClass Ω₂] [Countable Ω₁] [Countable Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ω₁ × Ω₂)) (ε : ENNReal) (hE : ∀ᵐ x ∂μ, ν {y | (x,y) ∈ E} ≤ ε) :
    (μ.prod ν) E ≤ ε := by
  rw [Measure.prod_apply (Set.to_countable E).measurableSet]
  exact (lintegral_mono_ae hE).trans_eq (by simp)

#print axioms independent_countable_event_bound
end ConditionalSpectralExtremes
