import CoarseBoxDefinitions
import FiniteExponentialMaximal
import TiltedLogSineSums

/-! The actual path event A and positive kernel mass p_L in Section 3.
Arguments w are fine-block heights, not individual cycle increments.
The block law is the sum pushforward of the actual finite iid tilted
log-sine product, including q=0. Auxiliary noise is an explicit measure. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes.KernelPath
open FineScales CoarseBoxes

def pathEvent (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) :
    Set (Fin (count p n) → ℝ) :=
  {w | (∀ i : Fin (count p n), FiniteWalk.partialSum (i.val+1) w ≤
      fineFrontier p n κ q (i.val+1)-G) ∧
    terminalHeight p n κ q ≤ FiniteWalk.partialSum (count p n) w ∧
    FiniteWalk.partialSum (count p n) w ≤ terminalHeight p n κ q+1}

def pathWeight (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (w : Fin (count p n) → ℝ) : ℝ≥0∞ :=
  (pathEvent p n κ G q).indicator (fun w => ENNReal.ofReal
    (Real.exp (-criticalPoint κ*(FiniteWalk.partialSum (count p n) w-terminalHeight p n κ q)))) w

def referenceFineLaw (s : ℝ) (m : ℕ) (q : ℕ → ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun i : Fin m => (tiltedLogSineProduct s (q (i.val+1))).map logSineSum)

def referencePathMass (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (noise : Measure (Fin (count p n) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ w, ∫⁻ ζ, pathWeight p n κ G q (w+ζ) ∂noise
    ∂referenceFineLaw (criticalPoint κ) (count p n) q

theorem pathEvent_measurable (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) :
    MeasurableSet (pathEvent p n κ G q) := by
  apply MeasurableSet.inter
  · have he : (fun w : Fin (count p n) → ℝ => ∀ i : Fin (count p n),
        FiniteWalk.partialSum (i.val+1) w ≤ fineFrontier p n κ q (i.val+1)-G) =
        ⋂ i : Fin (count p n), {w | FiniteWalk.partialSum (i.val+1) w ≤
          fineFrontier p n κ q (i.val+1)-G} := Set.ofPred_forall _
    rw [he]
    exact MeasurableSet.iInter (fun _ => measurableSet_le
      (FiniteWalk.partialSum_measurable _ _) measurable_const)
  · exact (measurableSet_le measurable_const (FiniteWalk.partialSum_measurable _ _)).inter
      (measurableSet_le (FiniteWalk.partialSum_measurable _ _) measurable_const)

theorem pathWeight_measurable (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) :
    Measurable (pathWeight p n κ G q) := by
  apply Measurable.indicator _ (pathEvent_measurable p n κ G q)
  fun_prop

theorem pathWeight_le_one (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (w : Fin (count p n) → ℝ) : pathWeight p n κ G q w ≤ 1 := by
  by_cases hw : w ∈ pathEvent p n κ G q
  · rw [pathWeight, indicator_of_mem hw]
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (criticalPoint_pos hκ).le)
      (sub_nonneg.mpr hw.2.1)
  · rw [pathWeight, indicator_of_notMem hw]
    positivity

theorem referenceFineLaw_isProbabilityMeasure (s : ℝ) (hs : -1 < s) (m : ℕ) (q : ℕ → ℕ) :
    IsProbabilityMeasure (referenceFineLaw s m q) := by
  have hi (i : Fin m) : IsProbabilityMeasure
      ((tiltedLogSineProduct s (q (i.val+1))).map logSineSum) := by
    let _ := tiltedLogSineProduct_isProbabilityMeasure s (q (i.val+1)) hs
    exact Measure.isProbabilityMeasure_map (by unfold logSineSum; fun_prop)
  let _ := hi
  unfold referenceFineLaw
  infer_instance

theorem referencePathMass_le_one (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (noise : Measure (Fin (count p n) → ℝ)) [IsProbabilityMeasure noise] :
    referencePathMass p n κ G q noise ≤ 1 := by
  let _ := referenceFineLaw_isProbabilityMeasure (criticalPoint κ)
    (by linarith [criticalPoint_pos hκ]) (count p n) q
  calc
    _ ≤ ∫⁻ _w : Fin (count p n) → ℝ, ∫⁻ _ζ : Fin (count p n) → ℝ,
        (1 : ℝ≥0∞) ∂noise ∂referenceFineLaw (criticalPoint κ) (count p n) q := by
      apply lintegral_mono
      intro w
      apply lintegral_mono
      intro ζ
      exact pathWeight_le_one p n κ G q hκ (w+ζ)
    _ = 1 := by simp

#print axioms pathEvent_measurable
#print axioms pathWeight_measurable
#print axioms pathWeight_le_one
#print axioms referenceFineLaw_isProbabilityMeasure
#print axioms referencePathMass_le_one

end ConditionalSpectralExtremes.KernelPath
