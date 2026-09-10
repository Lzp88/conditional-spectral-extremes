import CoarseSamplePrefixes

/-! Every fine endpoint belongs to an actual coarse group, including
the final endpoint. This is proved from the literal grouping algorithm. -/
noncomputable section
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales

theorem groupBlocks_prefix (p : Parameters) (n : Nat) :
    ∀ j ≤ groupNumber p n, blockPrefix (groupBlocks p n) j=groupStart p n j := by
  intro j
  induction j with
  | zero => intro _; simp [blockPrefix, group_start_zero]
  | succ j ih =>
    intro hj
    have hj' : j < groupNumber p n := by omega
    rw [blockPrefix_step, ih (by omega), group_start_step p n j hj']

theorem actual_fine_endpoint_in_group (p : Parameters) (n : Nat)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (k : Nat) (hk : 0 < k) (hkm : k ≤ count p n) :
    ∃ j : Fin (groupNumber p n), ∃ i : Nat,
      0 < i ∧ i ≤ groupBlocks p n j ∧ k=groupStart p n j+i := by
  have htotal : blockPrefix (groupBlocks p n) (groupNumber p n)=count p n := by
    rw [groupBlocks_prefix p n _ le_rfl, groupStart_last p n hv hm]
  let z : Fin (blockPrefix (groupBlocks p n) (groupNumber p n)) := ⟨k-1, by rw [htotal]; omega⟩
  let a := (orderedBlockEquiv (groupNumber p n) (groupBlocks p n)).symm z
  have he := congrArg Fin.val ((orderedBlockEquiv (groupNumber p n) (groupBlocks p n)).apply_symm_apply z)
  change blockPrefix (groupBlocks p n) a.1+a.2.val=k-1 at he
  rw [groupBlocks_prefix p n a.1 a.1.isLt.le] at he
  refine ⟨a.1,a.2.val+1,by omega,by have := a.2.isLt; omega,by omega⟩

#print axioms actual_fine_endpoint_in_group
end ConditionalSpectralExtremes.IIDRegroup
