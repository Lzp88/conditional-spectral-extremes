import KilledGroupLaw

/-! Exact identification of the killed endpoint transition measure, for
every initial height and every measurable endpoint set. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem killedGroupKernelENN_endpoint_integral {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ x' in A, killedGroupKernelENN s n times barrier x x') =
      tiltedLogSineProduct s (n+1)
        (killedGroupEvent (n+1) times barrier x ∩ (fun y => (∑ i, y i)+x) ⁻¹' A) := by
  let E := killedGroupEvent (n+1) times barrier x
  have hE : MeasurableSet E := killedGroupEvent_measurable (n+1) times barrier x
  let A' : Set ℝ := (fun d => d+x) ⁻¹' A
  have hA' : MeasurableSet A' := hA.preimage (by fun_prop)
  have hKm : Measurable (fun x' => killedGroupKernelENN s n times barrier x x') := by
    simpa only [Function.comp_def] using!
      (killedGroupKernelENN_measurable s n times barrier).comp (measurable_const.prodMk measurable_id)
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) x).lintegral_comp (hKm.indicator hA)
  rw [← lintegral_indicator hA]
  rw [← hshift]
  have he := actual_bridge_endpoint_probability s hs n E hE A' hA'
  rw [← lintegral_indicator hA'] at he
  have hset : E ∩ (fun y : Fin (n+1) → ℝ => ∑ i, y i) ⁻¹' A' =
      killedGroupEvent (n+1) times barrier x ∩ (fun y : Fin (n+1) → ℝ => (∑ i, y i)+x) ⁻¹' A := by
    rfl
  rw [hset] at he
  rw [← he]
  apply lintegral_congr
  intro d
  have hmem : d ∈ A' ↔ d+x ∈ A := Iff.rfl
  by_cases hd : d ∈ A'
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem (hmem.mp hd)]
    unfold killedGroupKernelENN
    congr 1
    ring
  · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem (hmem.not.mp hd)]

def killedEndpointLaw {ι : Type*} (s : ℝ) (n : ℕ) (times : ι → ℕ)
    (barrier : ι → ℝ) (x : ℝ) : Measure ℝ :=
  ((tiltedLogSineProduct s (n+1)).restrict (killedGroupEvent (n+1) times barrier x)).map
    (fun y => (∑ i, y i)+x)

theorem killedEndpointLaw_eq_withDensity {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ) :
    killedEndpointLaw s n times barrier x =
      volume.withDensity (fun x' => killedGroupKernelENN s n times barrier x x') := by
  have hsum : Measurable (fun y : Fin (n+1) → ℝ => (∑ i, y i)+x) := by fun_prop
  apply Measure.ext
  intro A hA
  rw [killedEndpointLaw, Measure.map_apply hsum hA, Measure.restrict_apply (hA.preimage hsum),
    withDensity_apply _ hA, killedGroupKernelENN_endpoint_integral s hs n times barrier x A hA,
    inter_comm]

#print axioms killedGroupKernelENN_endpoint_integral
#print axioms killedEndpointLaw_eq_withDensity

end ConditionalSpectralExtremes
