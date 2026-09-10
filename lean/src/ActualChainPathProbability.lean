import CoarseAcceptanceToInner
import FreshGroupEvent

/-! The integrated actual endpoint chain is bounded by the probability
of the actual reference inner path, through the same iid samples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales CoarseBoxes KernelPath

theorem actual_endpoint_chain_le_inner_path (p : Parameters) (n : Nat) (κ G B₀ : Real) (q : Nat → Nat)
    (hκ : 0 < κ) (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 3 ≤ groupSamples p n q j) :
    actualEndpointChain p n κ G B₀ q ≤
      referenceFineLaw (criticalPoint κ) (count p n) q (innerPathEvent p n κ G q) := by
  let free : Fin (groupNumber p n) → Nat := fun j => groupSamples p n q j-1
  let fine : Fin (groupNumber p n) → Nat := fun j => groupBlocks p n j+1
  let times : (j : Fin (groupNumber p n)) → Fin (fine j) → Nat := fun j i => groupTime p n q j i
  let barrier : (j : Fin (groupNumber p n)) → Fin (fine j) → Real := fun j i => groupBarrier p n κ G q j i
  let lo : Fin (groupNumber p n) → Real := fun j => endpointLower p n κ G B₀ q (j.val+1)
  let hi : Fin (groupNumber p n) → Real := fun j => endpointUpper p n κ G B₀ q (j.val+1)
  let E := freshGroupEvent (groupNumber p n) free fine times barrier lo hi 0
  have hqp : ∀ j < groupNumber p n, 0 < groupSamples p n q j := fun j hj => by have := hq j hj; omega
  have hmap := coarseToFinePath_measurePreserving p n q hv hm hqp (criticalPoint κ) (by linarith [criticalPoint_pos hκ])
  have hsub : E ⊆ (coarseToFinePath p n q hv hm hqp) ⁻¹' innerPathEvent p n κ G q := by
    intro x hx
    have hg := freshGroupEvent_group (groupNumber p n) free fine times barrier lo hi 0 x hx
    apply coarse_acceptance_to_inner p n κ G B₀ q hκ hv hm hqp x
    · intro j
      simpa only [zero_add, free, fine, times, barrier, coarseSampleSizes, blockSums] using! (hg j).1
    · intro j
      simpa only [zero_add, free, lo, hi, coarseSampleSizes, blockSums] using! (hg j).2
  rw [actualEndpointChain_eq_fresh p n κ G B₀ q hκ hq]
  change freshGroupBoxProbability (criticalPoint κ) (groupNumber p n) free fine times barrier lo hi 0 ≤ _
  rw [← freshGroupEvent_probability (criticalPoint κ) (by linarith [criticalPoint_pos hκ])]
  exact (measure_mono hsub).trans_eq (hmap.measure_preimage (innerPathEvent_measurable p n κ G q).nullMeasurableSet)

#print axioms actual_endpoint_chain_le_inner_path
end ConditionalSpectralExtremes.IIDRegroup
