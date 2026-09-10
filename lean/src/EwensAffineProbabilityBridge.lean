import EwensAffineCharacteristic
import EwensProfileMeasureBridge

/-! Affine cycle-count events are exactly events of the original finite Ewens law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes

theorem ewensAffineMeasure_real (θ : Real) (hθ : 0 < θ) (n : Nat) (a b : Real)
    (E : Set Real) (hE : MeasurableSet E) :
    (ewensAffineMeasure θ n a b).real E=
      ewensProbability θ n (fun c => ((cycleCount c : Real)-a)/b ∈ E) := by
  rw [measureReal_def,ewensAffineMeasure,Measure.map_apply (measurable_of_countable _) hE,
    ← measureReal_def,ewensProfileLaw_real θ hθ n]
  rfl

#print axioms ewensAffineMeasure_real
end ConditionalSpectralExtremes
