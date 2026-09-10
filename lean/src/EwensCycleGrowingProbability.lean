import EwensCycleTightness
import EwensAffineProbabilityBridge

/-! Tightness expressed directly using the manuscript's finite ewensProbability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ewens_clt_growing_probability (θ : Real) (hθ : 0 < θ) (b : Nat → Real)
    (hb : Tendsto b atTop atTop) :
    Tendsto (fun n : Nat => ewensProbability θ n (fun c =>
      b n ≤ |((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)|)) atTop (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (ewens_clt_growing_tail θ hθ b hb)
  simp only [ENNReal.toReal_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  change (ewensAffineMeasure θ n (θ*Real.log n) (Real.sqrt (θ*Real.log n))).real {x | b n ≤ |x|}=_
  exact ewensAffineMeasure_real θ hθ n _ _ _ (isClosed_le continuous_const continuous_abs).measurableSet

#print axioms ewens_clt_growing_probability
end ConditionalSpectralExtremes
