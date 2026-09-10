import PointwiseBridgeConvolution
import PointwiseBridgeProbability
import BridgePathAlgebra

/-! A measure whose total mass is the endpoint density, obtained from the
actual q-1 dimensional Lebesgue integral. It is not normalized and is not
introduced as conditioning a probability measure on a null event. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def bridgeEndpointMeasure (f : ℝ → ℝ) (n : ℕ) (d : ℝ) : Measure (Fin (n+1) → ℝ) :=
  (volume.withDensity (fun x : Fin n → ℝ =>
    ∏ i, ENNReal.ofReal (f (bridgePath n d x i)))).map (bridgePath n d)

theorem pointwiseBridge_eq_measure (f : ℝ → ℝ) (n : ℕ) (d : ℝ)
    (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    pointwiseBridge f n d E = bridgeEndpointMeasure f n d E := by
  classical
  rw [bridgeEndpointMeasure, Measure.map_apply (bridgePath_measurable n d) hE,
    withDensity_apply _ (hE.preimage (bridgePath_measurable n d)),
    ← lintegral_indicator (hE.preimage (bridgePath_measurable n d))]
  apply lintegral_congr
  intro x
  by_cases hx : bridgePath n d x ∈ E <;> simp [hx]

theorem bridgeEndpointMeasure_univ (f : ℝ → ℝ) (n : ℕ) (d : ℝ) :
    bridgeEndpointMeasure f n d univ = pointwiseBridge f n d univ :=
  (pointwiseBridge_eq_measure f n d univ .univ).symm

theorem bridgeEndpointMeasure_total_ae (f : ℝ → ℝ) (n : ℕ) (d : ℝ) :
    ∀ᵐ x ∂bridgeEndpointMeasure f n d, (∑ i, x i) = d := by
  rw [ae_iff]
  have hE : MeasurableSet {x : Fin (n+1) → ℝ | ¬ (∑ i, x i) = d} := by
    apply MeasurableSet.compl
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  rw [bridgeEndpointMeasure, Measure.map_apply (bridgePath_measurable n d) hE]
  have he : bridgePath n d ⁻¹' {x : Fin (n+1) → ℝ | ¬ (∑ i, x i) = d} = ∅ := by
    ext x
    simp [bridgePath_sum]
  rw [he, measure_empty]

theorem tiltedBridgeEndpointMeasure_finite (β : ℝ) (hβ : -1 < β)
    (n : ℕ) (hn : 2 ≤ n) (d : ℝ) :
    IsFiniteMeasure (bridgeEndpointMeasure (tiltedDensity β) n d) := by
  constructor
  rw [bridgeEndpointMeasure_univ, pointwiseBridge_tilted_eq_power β hβ n hn d]
  exact ENNReal.ofReal_lt_top

theorem bridgeEndpointMeasure_reverse (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (d : ℝ) :
    (bridgeEndpointMeasure f n d).map (reversePath (n+1)) = bridgeEndpointMeasure f n d := by
  ext E hE
  rw [Measure.map_apply (reversePath_measurable (n+1)) hE,
    ← pointwiseBridge_eq_measure f n d _ (hE.preimage (reversePath_measurable (n+1))),
    pointwiseBridge_reverse f hf n d E hE, pointwiseBridge_eq_measure f n d E hE]

#print axioms pointwiseBridge_eq_measure
#print axioms bridgeEndpointMeasure_univ
#print axioms bridgeEndpointMeasure_total_ae
#print axioms tiltedBridgeEndpointMeasure_finite
#print axioms bridgeEndpointMeasure_reverse

end ConditionalSpectralExtremes
