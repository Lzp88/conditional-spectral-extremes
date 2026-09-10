import OrdinaryJointDefinitions

/-! The exact diagonal push-forward of the already proved ordinary cycle CLT. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ewens_diagonal_map (θ : Real) (n : Nat) :
    (ewensCLTMeasure θ n).map (fun x : Real => (x,x)) =
      (ewensProfileLaw θ n).map (ordinaryDiagonal θ n) := by
  unfold ewensCLTMeasure ewensAffineMeasure
  rw [Measure.map_map (by fun_prop) (measurable_of_countable _)]
  rfl

theorem ordinary_diagonal_central_limit (θ : Real) (hθ : 0 < θ) :
    Tendsto (fun n : Nat => ((ewensCLTLaw θ hθ n).map
      (show Continuous (fun x : Real => (x,x)) by fun_prop).measurable.aemeasurable))
      atTop (𝓝 diagonalGaussianLaw) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (ewens_cycle_central_limit θ hθ) (by fun_prop)

#print axioms ordinary_diagonal_central_limit
end ConditionalSpectralExtremes
