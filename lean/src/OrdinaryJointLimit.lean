import OrdinaryJointApproximation
import OrdinaryDiagonalLimit
import VaryingMeasureSlutsky

/-! The actual joint ordinary-Ewens limit (G,G), with one shared Gaussian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ordinary_ewens_joint_limit (hmain : ExactCycleLocalization) (θ : Real) (hθ : 0 < θ) :
    Tendsto (ewensJointLaw θ hθ) atTop (𝓝 diagonalGaussianLaw) := by
  let μ : (n : Nat) → Measure (Configuration n) := ewensProfileLaw θ
  let _ : ∀ n, IsProbabilityMeasure (μ n) := fun n => ewensProfileLaw_probability θ hθ n
  have hX (n : Nat) : Measurable (ordinaryDiagonal θ n) := measurable_of_countable _
  have hY (n : Nat) : Measurable (ordinaryJoint θ n) := measurable_of_countable _
  have hweak : Tendsto (fun n : Nat =>
      (⟨(μ n).map (ordinaryDiagonal θ n),Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩ :
        ProbabilityMeasure (Real × Real))) atTop
          (@nhds (ProbabilityMeasure (Real × Real)) inferInstance diagonalGaussianLaw) := by
    apply (ordinary_diagonal_central_limit θ hθ).congr'
    apply Eventually.of_forall
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    change (ewensCLTMeasure θ n).map (fun x : Real => (x,x))=_
    exact ewens_diagonal_map θ n
  exact varying_measure_slutsky μ (ordinaryDiagonal θ) (ordinaryJoint θ) hX hY
    diagonalGaussianLaw hweak (ordinary_joint_approximation hmain θ hθ)

#print axioms ordinary_ewens_joint_limit
end ConditionalSpectralExtremes
