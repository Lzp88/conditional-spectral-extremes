import EwensProfileMeasureBridge

/-! The genuine natural-valued cycle-count law, obtained from the actual
ordinary profile measure, with its exact coefficient masses and PGF. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

def ewensCycleCountLaw (θ : Real) (n : Nat) : Measure Nat :=
  (ewensProfileLaw θ n).map cycleCount

theorem ewensCycleCountLaw_probability (θ : Real) (hθ : 0 < θ) (n : Nat) :
    IsProbabilityMeasure (ewensCycleCountLaw θ n) := by
  let _ : IsProbabilityMeasure (ewensProfileLaw θ n) := ewensProfileLaw_probability θ hθ n
  exact MeasureTheory.Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem ewensCycleCountLaw_singleton (θ : Real) (hθ : 0 < θ) (n k : Nat) :
    ewensCycleCountLaw θ n {k}=ENNReal.ofReal (θ^k*coefficient n k/ewensPartition θ n) := by
  rw [ewensCycleCountLaw,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k),
    ewensProfileLaw_apply θ hθ n]
  simp only [mem_preimage,mem_singleton_iff,ewensProbability,ewensMass_count]

theorem ewensCycleCountLaw_PGF (θ : Real) (hθ : 0 < θ) (n : Nat) (u : Complex) :
    (∫ k, u^k ∂ewensCycleCountLaw θ n)=markerValue n ((θ : Complex)*u)/markerValue n (θ : Complex) := by
  rw [ewensCycleCountLaw,integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  exact ewensProfileLaw_PGF θ hθ n u

#print axioms ewensCycleCountLaw_singleton
#print axioms ewensCycleCountLaw_PGF
end ConditionalSpectralExtremes
