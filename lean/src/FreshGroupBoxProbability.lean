import ActualKilledBoxChain
import BoxChainInitialMeasurability

/-! The box-chain integral is the survival probability of sequential
fresh groups of actual iid tilted log-sine increments. Each transition
is proved from the actual increment probability law. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes

def freshGroupBoxProbability (s : ℝ) : (B : ℕ) → (free fine : Fin B → ℕ) →
    (times : ∀ j, Fin (fine j) → ℕ) → (barrier : ∀ j, Fin (fine j) → ℝ) →
    (lo hi : Fin B → ℝ) → ℝ → ℝ≥0∞
  | 0, _, _, _, _, _, _, _ => 1
  | B+1, free, fine, times, barrier, lo, hi, x =>
      ∫⁻ y in killedGroupEvent (free 0+1) (times 0) (barrier 0) x,
        (Icc (lo 0) (hi 0)).indicator
          (freshGroupBoxProbability s B (fun j => free j.succ) (fun j => fine j.succ)
            (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi))
          ((∑ i, y i)+x) ∂tiltedLogSineProduct s (free 0+1)

theorem actualKilledBoxChain_succ_fresh (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin (B+1) → ℕ) (hfree : ∀ j, 2 ≤ free j)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin (B+1) → ℝ) (x : ℝ) :
    actualKilledBoxChain s (B+1) free fine times barrier lo hi x =
      ∫⁻ y in killedGroupEvent (free 0+1) (times 0) (barrier 0) x,
        (Icc (lo 0) (hi 0)).indicator
          (actualKilledBoxChain s B (fun j => free j.succ) (fun j => fine j.succ)
            (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi))
          ((∑ i, y i)+x) ∂tiltedLogSineProduct s (free 0+1) := by
  have hK : ∀ j : Fin (B+1), Measurable (fun p : ℝ × ℝ =>
      killedGroupKernelENN s (free j) (times j) (barrier j) p.1 p.2) :=
    fun j => killedGroupKernelENN_measurable s (free j) (times j) (barrier j)
  have hfinite : ∀ j : Fin (B+1), ∀ x x',
      killedGroupKernelENN s (free j) (times j) (barrier j) x x' ≠ ⊤ :=
    fun j x x' => pointwiseBridge_tilted_ne_top s hs (free j) (hfree j) (x'-x) _
  have htail : Measurable (actualKilledBoxChain s B (fun j => free j.succ)
      (fun j => fine j.succ) (fun j => times j.succ) (fun j => barrier j.succ)
      (Fin.tail lo) (Fin.tail hi)) :=
    boxChainIntegral_measurable_initial B _ (fun j => hK j.succ) _ _
  rw [← killedGroupKernelENN_test_integral s hs (free 0) (times 0) (barrier 0) x _
    (htail.indicator measurableSet_Icc)]
  unfold actualKilledBoxChain
  rw [boxChainIntegral_succ B _ hK hfinite, ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ Icc (lo 0) (hi 0)
  · simp only [indicator_of_mem ha]
  · simp only [indicator_of_notMem ha, mul_zero]

theorem freshGroupBoxProbability_eq_chain (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin B → ℕ) (hfree : ∀ j, 2 ≤ free j)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x : ℝ) :
    freshGroupBoxProbability s B free fine times barrier lo hi x =
      actualKilledBoxChain s B free fine times barrier lo hi x := by
  induction B generalizing x with
  | zero => exact (boxChainIntegral_zero _ _ _ x).symm
  | succ B ih =>
    rw [actualKilledBoxChain_succ_fresh s hs B free fine hfree times barrier lo hi x,
      freshGroupBoxProbability]
    apply lintegral_congr
    intro y
    by_cases hy : (∑ i, y i)+x ∈ Icc (lo 0) (hi 0)
    · simp only [indicator_of_mem hy]
      exact ih (fun j => free j.succ) (fun j => fine j.succ) (fun j => hfree j.succ)
        (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi) _
    · simp only [indicator_of_notMem hy]

#print axioms actualKilledBoxChain_succ_fresh
#print axioms freshGroupBoxProbability_eq_chain

end ConditionalSpectralExtremes
