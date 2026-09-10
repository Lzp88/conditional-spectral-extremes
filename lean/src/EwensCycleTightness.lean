import EwensCycleCLT

/-! Actual cycle-count tightness, including every growing standardized threshold,
for the ordinary-Ewens Taylor remainder in the final corollary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ewens_clt_tight (θ : Real) (hθ : 0 < θ) :
    IsTightMeasureSet (range (ewensCLTMeasure θ)) := by
  let _ (n : Nat) : IsProbabilityMeasure (ewensCLTMeasure θ n) :=
    ewensAffineMeasure_probability θ hθ n _ _
  exact isTightMeasureSet_of_tendsto_charFun
    (f := fun t : Real => Complex.exp (-(t : Complex)^2/2)) (by fun_prop)
    (ewens_cycle_charFun_tendsto θ hθ)

theorem ewens_clt_growing_tail (θ : Real) (hθ : 0 < θ) (b : Nat → Real)
    (hb : Tendsto b atTop atTop) :
    Tendsto (fun n : Nat => ewensCLTMeasure θ n {x | b n ≤ |x|}) atTop (𝓝 0) := by
  have ht := (tendsto_measure_norm_gt_of_isTightMeasureSet (ewens_clt_tight θ hθ)).comp
    (hb.atTop_div_const (by norm_num : (0 : Real)<2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hb.eventually_gt_atTop 0] with n hn
  apply le_iSup_of_le (ewensCLTMeasure θ n)
  apply le_iSup_of_le (mem_range_self n)
  apply measure_mono
  intro x hx
  change b n/2 < ‖x‖
  rw [Real.norm_eq_abs]
  change b n ≤ |x| at hx
  linarith

#print axioms ewens_clt_tight
#print axioms ewens_clt_growing_tail
end ConditionalSpectralExtremes
