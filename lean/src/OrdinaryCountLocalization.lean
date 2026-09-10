import EwensProbabilityEvents
import EwensCycleLLN

/-! Uniform exact-cycle localization transfers to the actual ordinary Ewens
law at its random count, with one fixed log-log constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ordinary_random_count_localization (hmain : ExactCycleLocalization)
    (θ : Real) (hθ : 0 < θ) :
    ∃ C : Real, 0 ≤ C ∧ Tendsto (fun n : Nat => ewensProbability θ n
      (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n (cycleCount c)|)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := hmain (θ/2) (2*θ) (by positivity) (by linarith)
  refine ⟨C,hC,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N,_hN,hnorm⟩ := hbound (ε/2) (by positivity)
  have htail := ewens_cycle_weak_law θ hθ (θ/2) (by positivity)
  apply Filter.eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (2 : Nat),
    htail.eventually (gt_mem_nhds (show (0 : Real)<ε/2 by positivity))] with n hn hn2 ht
  let E : Configuration n → Prop := fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n (cycleCount c)|
  let good : Nat → Prop := fun k => (θ/2)*Real.log n≤(k : Real) ∧ (k : Real)≤(2*θ)*Real.log n
  have hL : 0 < Real.log (n : Real) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc : ∀ k ∈ attainableCycleCounts n, good k → conditionalProbability n k E≤ε/2 := by
    intro k _ hk
    apply (conditionalProbability_mono_valid E
      (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n k|) ?_).trans
      (hnorm n hn k hk.1 hk.2).le
    intro c hc he
    simpa only [E,hc.2] using he
  have hm := ewensProbability_from_uniform_conditioning θ hθ n good E (ε/2) (by positivity) hc
  have hb : ewensProbability θ n (fun c => ¬good (cycleCount c)) ≤
      ewensProbability θ n (fun c => θ/2≤|(cycleCount c : Real)/Real.log n-θ|) := by
    apply ewensProbability_mono θ hθ n _ _
    intro c _ hbad
    by_contra hh
    have h := abs_lt.mp (lt_of_not_ge hh)
    apply hbad
    constructor
    · apply (le_div_iff₀ hL).mp
      linarith
    · apply (div_le_iff₀ hL).mp
      linarith
  have hp := ewensProbability_nonneg θ hθ n E
  change dist (ewensProbability θ n E) 0<ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hp]
  linarith

#print axioms ordinary_random_count_localization
end ConditionalSpectralExtremes
