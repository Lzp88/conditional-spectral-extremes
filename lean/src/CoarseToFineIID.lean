import CoarseSamplePrefixes
import OrderedBlockSegments

/-! The same coarse iid samples mapped into the original fine path. All
coarse boundaries and all internal fine inspection times are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales CoarseBoxes KernelPath

def castOrderedSamples {N M : Nat} (h : N=M) (x : Fin N → Real) : Fin M → Real :=
  fun i => x (Fin.cast h.symm i)

theorem castOrderedSamples_measurePreserving {N M : Nat} (h : N=M) (μ : Measure Real) :
    MeasurePreserving (castOrderedSamples h) (Measure.pi (fun _ : Fin N => μ))
      (Measure.pi (fun _ : Fin M => μ)) := by
  subst M
  exact MeasurePreserving.id _

theorem castOrderedSamples_partialSum {N M : Nat} (h : N=M) (x : Fin N → Real) (k : Nat) :
    FiniteWalk.partialSum k (castOrderedSamples h x)=FiniteWalk.partialSum k x := by
  subst M
  rfl

def coarseToFinePath (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j)
    (x : (j : Fin (groupNumber p n)) → Fin (coarseSampleSizes p n q j) → Real) : Fin (count p n) → Real :=
  orderedFineSums (count p n) (fun i => q (i+1))
    (castOrderedSamples (coarse_sample_total p n q hv hm hq)
      (orderedBlockSamplesEquiv (groupNumber p n) (coarseSampleSizes p n q) Real x))

theorem coarseToFinePath_measurePreserving (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j) (s : Real) (hs : -1 < s) :
    MeasurePreserving (coarseToFinePath p n q hv hm hq)
      (Measure.pi (fun j : Fin (groupNumber p n) => tiltedLogSineProduct s (coarseSampleSizes p n q j)))
      (referenceFineLaw s (count p n) q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  exact (actual_reference_fine_law_from_iid s hs (count p n) q).comp
    ((castOrderedSamples_measurePreserving (coarse_sample_total p n q hv hm hq) (tiltedLogSineLaw s)).comp
      (orderedBlockSamplesEquiv_measurePreserving (groupNumber p n) (coarseSampleSizes p n q) (tiltedLogSineLaw s)))

theorem coarseToFinePath_prefix (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j)
    (x : (j : Fin (groupNumber p n)) → Fin (coarseSampleSizes p n q j) → Real)
    (j : Nat) (hj : j ≤ groupNumber p n) :
    FiniteWalk.partialSum (groupStart p n j) (coarseToFinePath p n q hv hm hq x) =
      FiniteWalk.partialSum j (blockSums (groupNumber p n) (coarseSampleSizes p n q) x) := by
  rw [coarseToFinePath, actual_reference_fine_prefix _ _ q (groupStart_le_count p n j hv hm),
    castOrderedSamples_partialSum, ← coarse_sample_prefix p n q hq j hj,
    ← blockSums_partialSum (groupNumber p n) j (coarseSampleSizes p n q) hj x]

theorem coarseToFinePath_within_group (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j)
    (x : (j : Fin (groupNumber p n)) → Fin (coarseSampleSizes p n q j) → Real)
    (j : Fin (groupNumber p n)) (i : Nat) (hi : i ≤ groupBlocks p n j) :
    FiniteWalk.partialSum (groupStart p n j+i) (coarseToFinePath p n q hv hm hq x) =
      FiniteWalk.partialSum j (blockSums (groupNumber p n) (coarseSampleSizes p n q) x)+
        FiniteWalk.partialSum (groupTime p n q j i) (x j) := by
  have hib : groupStart p n j+i ≤ count p n := by
    have hh := groupStart_le_count p n (j.val+1) hv hm
    rw [group_start_step p n j j.isLt] at hh
    omega
  have ht : groupTime p n q j i ≤ coarseSampleSizes p n q j := by
    rw [coarseSampleSizes_eq p n q j (hq j j.isLt)]
    exact groupTime_le_samples p n q j i j.isLt hi
  have he : countPrefix q (groupStart p n j+i)=
      blockPrefix (coarseSampleSizes p n q) j+groupTime p n q j i := by
    rw [coarse_sample_prefix p n q hq j j.isLt.le]
    unfold groupTime
    have hh := countPrefix_mono q (by omega : groupStart p n j ≤ groupStart p n j+i)
    omega
  rw [coarseToFinePath, actual_reference_fine_prefix _ _ q hib, castOrderedSamples_partialSum, he,
    ordered_block_segment (groupNumber p n) (coarseSampleSizes p n q) j _ ht x,
    ← blockSums_partialSum (groupNumber p n) j (coarseSampleSizes p n q) j.isLt.le x]

#print axioms coarseToFinePath_measurePreserving
#print axioms coarseToFinePath_within_group
end ConditionalSpectralExtremes.IIDRegroup
