import OrderedBlockPartialSums

/-! Partial sums inside a block agree with increments of the one global
partial sum, including both endpoints of every block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup

theorem partialSum_add_segment (N a b : Nat) (hab : a+b ≤ N) (x : Fin N → Real) :
    FiniteWalk.partialSum (a+b) x = FiniteWalk.partialSum a x+
      ∑ v : Fin b, x ⟨a+v.val, by omega⟩ := by
  rw [partialSum_eq_sum_fin N (a+b) hab, partialSum_eq_sum_fin N a (by omega), Fin.sum_univ_add]
  rfl

theorem ordered_block_segment (m : Nat) (q : Nat → Nat) (i : Fin m) (v : Nat) (hv : v ≤ q i)
    (x : (i : Fin m) → Fin (q i) → Real) :
    FiniteWalk.partialSum (blockPrefix q i+v) (orderedBlockSamplesEquiv m q Real x) =
      FiniteWalk.partialSum (blockPrefix q i) (orderedBlockSamplesEquiv m q Real x)+
        FiniteWalk.partialSum v (x i) := by
  have hab : blockPrefix q i+v ≤ blockPrefix q m := by
    calc
      _ ≤ blockPrefix q i+q i := Nat.add_le_add_left hv _
      _ = blockPrefix q (i.val+1) := (blockPrefix_step q i).symm
      _ ≤ _ := blockPrefix_mono q (Nat.succ_le_of_lt i.isLt)
  rw [partialSum_add_segment _ _ _ hab, partialSum_eq_sum_fin (q i) v hv]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  have he : (⟨blockPrefix q i+w.val, by omega⟩ : Fin (blockPrefix q m)) =
      orderedBlockEquiv m q ⟨i,Fin.castLE hv w⟩ := by apply Fin.ext; rfl
  rw [he]
  exact orderedBlockSamplesEquiv_apply_component m q x i (Fin.castLE hv w)

#print axioms partialSum_add_segment
#print axioms ordered_block_segment
end ConditionalSpectralExtremes.IIDRegroup
