import ExactCycleLocalization
import OrdinaryJointLimit
import EwensCycleCountLaw

/-! The manuscript's ordinary Ewens corollary, discharged using the proved
conditional localization theorem and the actual finite Ewens law throughout. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ConditionalSpectralExtremes

theorem actual_ordinary_ewens_random_centering (θ : Real) (hθ : 0 < θ) :
    ∃ C : Real, 0 ≤ C ∧ Tendsto (fun n : Nat => ewensProbability θ n
      (fun c => C*Real.log (Real.log n) <
        |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|)) atTop (𝓝 0) :=
  ordinary_ewens_random_centering exact_cycle_localization θ hθ

theorem actual_ordinary_ewens_joint_limit (θ : Real) (hθ : 0 < θ) :
    Tendsto (ewensJointLaw θ hθ) atTop (𝓝 diagonalGaussianLaw) :=
  ordinary_ewens_joint_limit exact_cycle_localization θ hθ

theorem actual_ordinary_ewens_corollary (θ : Real) (hθ : 0 < θ) :
    0 < ordinarySlope θ ∧
    (∃ C : Real, 0 ≤ C ∧ Tendsto (fun n : Nat => ewensProbability θ n
      (fun c => C*Real.log (Real.log n) <
        |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|)) atTop (𝓝 0)) ∧
    Tendsto (ewensJointLaw θ hθ) atTop (𝓝 diagonalGaussianLaw) :=
  ⟨ordinarySlope_pos θ hθ,actual_ordinary_ewens_random_centering θ hθ,
    actual_ordinary_ewens_joint_limit θ hθ⟩

#print axioms actual_ordinary_ewens_random_centering
#print axioms actual_ordinary_ewens_joint_limit
#print axioms actual_ordinary_ewens_corollary
end ConditionalSpectralExtremes
