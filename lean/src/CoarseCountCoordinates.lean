import CoarseFineCoverage
import FineCountDefinitions
import CountPathEnvironment

/-! Exact ordered coarse subvectors of the manuscript's count vector.
The environment below is identified with the literal Regular environment,
including all fine endpoints and the original category indexing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales IIDRegroup FiniteWalk

theorem groupStart_mono_bounded (p : Parameters) (n : ℕ) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ groupNumber p n) : groupStart p n j ≤ groupStart p n k := by
  rw [← groupBlocks_prefix p n j (hjk.trans hk), ← groupBlocks_prefix p n k hk]
  exact blockPrefix_mono _ hjk

def coarseCountIndex (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) : Fin (groupBlocks p n j) ↪ Option (Fin (count p n+1)) where
  toFun i := some ⟨groupStart p n j+i.val+1, by
    have hg := groupStart_le_count p n (j.val+1) hv hm
    rw [group_start_step p n j j.isLt] at hg
    have hi := i.isLt
    omega⟩
  inj' := by
    intro i k h
    apply Fin.ext
    have hh := congrArg Fin.val (Option.some.inj h)
    dsimp only at hh
    omega

def coarseCountSet (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) : Finset (Option (Fin (count p n+1))) :=
  Finset.univ.map (coarseCountIndex p n hv hm j)

theorem coarseCountSet_disjoint (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    Pairwise (fun j k : Fin (groupNumber p n) =>
      Disjoint (coarseCountSet p n hv hm j) (coarseCountSet p n hv hm k)) := by
  classical
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
  obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hb
  have hh := congrArg Fin.val (Option.some.inj (hi.trans hl.symm))
  change groupStart p n j+i.val+1=groupStart p n k+l.val+1 at hh
  rcases lt_or_gt_of_ne hjk with h | h
  · have ht := groupStart_mono_bounded p n (Nat.succ_le_of_lt h) k.isLt.le
    rw [group_start_step p n j j.isLt] at ht
    have hi := i.isLt
    omega
  · have ht := groupStart_mono_bounded p n (Nat.succ_le_of_lt h) j.isLt.le
    rw [group_start_step p n k k.isLt] at ht
    have hl := l.isLt
    omega

theorem partialSum_eq_range {q t : ℕ} (ht : t ≤ q) (f : ℕ → ℝ) :
    partialSum t (fun i : Fin q => f i.val) = ∑ i ∈ Finset.range t, f i := by
  classical
  unfold partialSum
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    exact ⟨⟨i, (Finset.mem_range.mp hi).trans_le ht⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hi⟩, rfl⟩
  · intro i _
    rfl

theorem coarseCount_discrepancy (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) (κ : ℝ) (X : Option (Fin (count p n+1)) → ℕ)
    (t : ℕ) (ht : t ≤ groupBlocks p n j) :
    localDiscrepancy (omega p n) κ (fineCountSequence p n X) (groupStart p n j) t =
      partialSum t (fun i => (X (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n) := by
  have he : (fun i => (X (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n) =
      fun i : Fin (groupBlocks p n j) =>
        (fineCountSequence p n X (groupStart p n j+i.val+1) : ℝ)-κ*omega p n := by
    funext i
    have hg := groupStart_le_count p n (j.val+1) hv hm
    rw [group_start_step p n j j.isLt] at hg
    rw [fineCountSequence_apply p n X _ (by have := i.isLt; omega)]
    rfl
  rw [he, partialSum_eq_range ht
    (fun i : ℕ => (fineCountSequence p n X (groupStart p n j+i+1) : ℝ)-κ*omega p n)]
  unfold localDiscrepancy
  rw [countPrefix_difference, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem coarseCount_environment (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) (κ : ℝ) (X : Option (Fin (count p n+1)) → ℕ) :
    environmentE p n κ (fineCountSequence p n X) j =
      countPathEnvironment (groupWidth p n j) (κ*omega p n)
        (fun i => X (coarseCountIndex p n hv hm j i)) := by
  have he : localMaximum (omega p n) κ (fineCountSequence p n X) (groupStart p n j) (groupBlocks p n j) =
      countPathMaximum (κ*omega p n) (fun i => X (coarseCountIndex p n hv hm j i)) := by
    unfold localMaximum countPathMaximum
    apply Finset.sup'_congr _ rfl
    intro t ht
    rw [coarseCount_discrepancy p n hv hm j κ X t (by have := Finset.mem_range.mp ht; omega)]
  unfold environmentE localE countPathEnvironment groupWidth
  rw [he]

#print axioms groupStart_mono_bounded
#print axioms coarseCountIndex
#print axioms coarseCountSet_disjoint
#print axioms partialSum_eq_range
#print axioms coarseCount_discrepancy
#print axioms coarseCount_environment

end ConditionalSpectralExtremes.BlockCounts
