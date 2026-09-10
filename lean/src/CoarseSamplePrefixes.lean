import ReferenceIIDRegrouping
import ActualEndpointChainDefinitions

/-! The exact coarse sample counts used by the killed-kernel chain have
the same cumulative lengths as the original fine-block counts. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales CoarseBoxes

def coarseSampleSizes (p : Parameters) (n : Nat) (q : Nat → Nat) (j : Nat) : Nat :=
  groupSamples p n q j-1+1

theorem coarseSampleSizes_eq (p : Parameters) (n : Nat) (q : Nat → Nat) (j : Nat)
    (hq : 0 < groupSamples p n q j) : coarseSampleSizes p n q j=groupSamples p n q j := by
  unfold coarseSampleSizes
  omega

theorem coarse_sample_prefix (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j) :
    ∀ j ≤ groupNumber p n, blockPrefix (coarseSampleSizes p n q) j=countPrefix q (groupStart p n j) := by
  intro j
  induction j with
  | zero => intro _; simp [blockPrefix, group_start_zero, countPrefix_zero]
  | succ j ih =>
    intro hj
    have hj' : j < groupNumber p n := by omega
    rw [blockPrefix_step, ih (by omega), coarseSampleSizes_eq p n q j (hq j hj')]
    unfold groupSamples
    have hh := countPrefix_mono q (by
      rw [group_start_step p n j hj']
      omega : groupStart p n j ≤ groupStart p n (j+1))
    omega

theorem coarse_sample_total (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hq : ∀ j < groupNumber p n, 0 < groupSamples p n q j) :
    blockPrefix (coarseSampleSizes p n q) (groupNumber p n)=countPrefix q (count p n) := by
  rw [coarse_sample_prefix p n q hq _ le_rfl, groupStart_last p n hv hm]

#print axioms coarse_sample_prefix
#print axioms coarse_sample_total
end ConditionalSpectralExtremes.IIDRegroup
