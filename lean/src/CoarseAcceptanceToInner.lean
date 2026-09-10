import CoarseToFineIID
import CoarseFineCoverage
import PathNoiseAbsorption

/-! Actual accepted coarse groups imply the original stronger fine path
event, including its narrow terminal interval. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales CoarseBoxes KernelPath

theorem partialSum_succ_blockSums (B : Nat) (Q : Nat → Nat)
    (x : (j : Fin B) → Fin (Q j) → Real) (j : Fin B) :
    FiniteWalk.partialSum (j.val+1) (blockSums B Q x) =
      FiniteWalk.partialSum j (blockSums B Q x)+∑ v, x j v := by
  rw [partialSum_add_segment B j.val 1 (Nat.succ_le_of_lt j.isLt)]
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.add_zero]
  rfl

theorem coarse_acceptance_to_inner (p : Parameters) (n : Nat) (κ G B₀ : Real) (q : Nat → Nat)
    (hκ : 0 < κ) (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j)
    (x : (j : Fin (groupNumber p n)) → Fin (coarseSampleSizes p n q j) → Real)
    (hkill : ∀ j : Fin (groupNumber p n), x j ∈ killedGroupEvent (coarseSampleSizes p n q j)
      (fun i : Fin (groupBlocks p n j+1) => groupTime p n q j i)
      (fun i : Fin (groupBlocks p n j+1) => groupBarrier p n κ G q j i)
      (FiniteWalk.partialSum j (blockSums (groupNumber p n) (coarseSampleSizes p n q) x)))
    (hbox : ∀ j : Fin (groupNumber p n),
      FiniteWalk.partialSum (j.val+1) (blockSums (groupNumber p n) (coarseSampleSizes p n q) x) ∈
        Icc (endpointLower p n κ G B₀ q (j.val+1)) (endpointUpper p n κ G B₀ q (j.val+1))) :
    coarseToFinePath p n q hv hm hq x ∈ innerPathEvent p n κ G q := by
  have hB : 0 < groupNumber p n :=
    List.length_pos_iff.mpr (ConditionalSpectralAudit.DyadicGrouping.dyadic_groups_nonempty _ _ hv hm)
  have ht : FiniteWalk.partialSum (count p n) (coarseToFinePath p n q hv hm hq x) ∈
      Icc (terminalHeight p n κ q+2/5) (terminalHeight p n κ q+3/5) := by
    let j : Fin (groupNumber p n) := ⟨groupNumber p n-1,by omega⟩
    have hh := hbox j
    have hj : j.val+1=groupNumber p n := by dsimp [j]; omega
    rw [hj, ← coarseToFinePath_prefix p n q hv hm hq x _ le_rfl, groupStart_last p n hv hm] at hh
    have hrad : endpointRadius p n (groupNumber p n)=1/10 := by
      simp [endpointRadius, Nat.ne_of_gt hB]
    unfold endpointLower endpointUpper at hh
    rw [boxCenter_last p n κ G B₀ q hκ hv hm, hrad] at hh
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  refine ⟨?_,ht.1,ht.2⟩
  intro k
  obtain ⟨j,i,_hip,hi,he⟩ := actual_fine_endpoint_in_group p n hv hm (k.val+1) (by omega) (Nat.succ_le_of_lt k.isLt)
  have hh := hkill j (⟨i,Nat.lt_succ_of_le hi⟩ : Fin (groupBlocks p n j+1))
  change FiniteWalk.partialSum j (blockSums (groupNumber p n) (coarseSampleSizes p n q) x)+
    FiniteWalk.partialSum (groupTime p n q j i) (x j) ≤ groupBarrier p n κ G q j i at hh
  rw [← coarseToFinePath_within_group p n q hv hm hq x j i hi] at hh
  simpa only [groupBarrier, ← he] using hh

#print axioms coarse_acceptance_to_inner
end ConditionalSpectralExtremes.IIDRegroup
