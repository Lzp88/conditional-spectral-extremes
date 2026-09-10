import BridgeDisintegration
import KilledGroupDefinitions

/-! The killed kernel is a genuine subprobability transition density.
Its row integral is proved to be the actual iid probability of surviving
the fine barriers; joint measurability is also proved from the defining
finite-dimensional integral. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def killedGroupKernelENN {ι : Type*} (s : ℝ) (n : ℕ) (times : ι → ℕ)
    (barrier : ι → ℝ) (x x' : ℝ) : ℝ≥0∞ :=
  pointwiseBridge (tiltedDensity s) n (x'-x) (killedGroupEvent (n+1) times barrier x)

theorem killedGroupKernelENN_measurable {ι : Type*} [Countable ι]
    (s : ℝ) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) :
    Measurable (fun p : ℝ × ℝ => killedGroupKernelENN s n times barrier p.1 p.2) := by
  let path : ((ℝ × ℝ) × (Fin n → ℝ)) → (Fin (n+1) → ℝ) :=
    fun p => bridgePath n (p.1.2-p.1.1) p.2
  have hpath : Measurable path := by
    exact (bridgePath_joint_measurable n).comp
      (Measurable.prodMk (by fun_prop) measurable_snd)
  let A : Set ((ℝ × ℝ) × (Fin n → ℝ)) :=
    {p | ∀ i, p.1.1+FiniteWalk.partialSum (times i) (path p) ≤ barrier i}
  have hA : MeasurableSet A := by
    simp only [A, ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    unfold FiniteWalk.partialSum
    fun_prop
  have hw : Measurable (fun p : (ℝ × ℝ) × (Fin n → ℝ) =>
      ∏ i, ENNReal.ofReal (tiltedDensity s (path p i))) := by
    have hd := tiltedDensity_measurable s
    fun_prop
  have hh := (hw.indicator hA).lintegral_prod_right' (ν := (volume : Measure (Fin n → ℝ)))
  convert! hh using 1

theorem killedGroupKernel_measurable {ι : Type*} [Countable ι]
    (s : ℝ) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) :
    Measurable (fun p : ℝ × ℝ => killedGroupKernel s n times barrier p.1 p.2) := by
  exact (killedGroupKernelENN_measurable s n times barrier).ennreal_toReal

theorem killedGroupKernelENN_rowmass {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ) :
    (∫⁻ x' : ℝ, killedGroupKernelENN s n times barrier x x') =
      tiltedLogSineProduct s (n+1) (killedGroupEvent (n+1) times barrier x) := by
  have hE := killedGroupEvent_measurable (n+1) times barrier x
  have hm := pointwiseBridge_measurable_endpoint _ (tiltedDensity_measurable s) n _ hE
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) (-x)).lintegral_comp hm
  have hshift' : (∫⁻ x' : ℝ, killedGroupKernelENN s n times barrier x x') =
      ∫⁻ d : ℝ, pointwiseBridge (tiltedDensity s) n d (killedGroupEvent (n+1) times barrier x) := by
    simpa only [killedGroupKernelENN, sub_eq_add_neg] using! hshift
  rw [hshift', pointwiseBridge_disintegrate _ (tiltedDensity_measurable s) n _ hE]
  exact (tiltedLogSineProduct_event_density s (n+1) hs _ hE).symm

theorem killedGroupKernelENN_rowmass_le_one {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ) :
    (∫⁻ x' : ℝ, killedGroupKernelENN s n times barrier x x') ≤ 1 := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure s (n+1) hs
  rw [killedGroupKernelENN_rowmass s hs n times barrier x]
  calc
    _ ≤ tiltedLogSineProduct s (n+1) univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

theorem killedGroupKernel_ofReal_eq {ι : Type*} (s : ℝ) (hs : -1 < s)
    (n : ℕ) (hn : 2 ≤ n) (times : ι → ℕ) (barrier : ι → ℝ) (x x' : ℝ) :
    ENNReal.ofReal (killedGroupKernel s n times barrier x x') =
      killedGroupKernelENN s n times barrier x x' := by
  exact ENNReal.ofReal_toReal (pointwiseBridge_tilted_ne_top s hs n hn (x'-x) _)

theorem killedGroupKernel_rowmass_le_one {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ) :
    (∫⁻ x' : ℝ, ENNReal.ofReal (killedGroupKernel s n times barrier x x')) ≤ 1 := by
  apply le_trans _ (killedGroupKernelENN_rowmass_le_one s hs n times barrier x)
  apply lintegral_mono
  intro x'
  exact ENNReal.ofReal_toReal_le

#print axioms killedGroupKernelENN_measurable
#print axioms killedGroupKernel_measurable
#print axioms killedGroupKernelENN_rowmass
#print axioms killedGroupKernelENN_rowmass_le_one
#print axioms killedGroupKernel_ofReal_eq
#print axioms killedGroupKernel_rowmass_le_one

end ConditionalSpectralExtremes
