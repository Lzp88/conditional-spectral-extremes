import OrderedIIDBlocks
import BridgePathAlgebra

/-! Every block prefix is exactly the corresponding prefix of the same
ordered underlying iid increments. No distributional replacement occurs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup

theorem orderedBlockSamplesEquiv_apply_component (m : Nat) (q : Nat → Nat) {Ω : Type*}
    [MeasurableSpace Ω] (x : (i : Fin m) → Fin (q i) → Ω) (i : Fin m) (v : Fin (q i)) :
    orderedBlockSamplesEquiv m q Ω x (orderedBlockEquiv m q ⟨i,v⟩) = x i v := by
  have hh := congrFun (congrFun ((orderedBlockSamplesEquiv m q Ω).symm_apply_apply x) i) v
  exact hh

theorem orderedBlockEquiv_cast_prefix (m k : Nat) (q : Nat → Nat) (hk : k ≤ m)
    (i : Fin k) (v : Fin (q i)) :
    Fin.castLE (blockPrefix_mono q hk) (orderedBlockEquiv k q ⟨i,v⟩) =
      orderedBlockEquiv m q ⟨Fin.castLE hk i,v⟩ := by
  apply Fin.ext
  rfl

theorem ordered_block_partial_sum (m k : Nat) (q : Nat → Nat) (hk : k ≤ m)
    (x : (i : Fin m) → Fin (q i) → Real) :
    FiniteWalk.partialSum (blockPrefix q k) (orderedBlockSamplesEquiv m q Real x) =
      ∑ i : Fin k, ∑ v : Fin (q i), x (Fin.castLE hk i) v := by
  rw [partialSum_eq_sum_fin _ _ (blockPrefix_mono q hk)]
  rw [← (orderedBlockEquiv k q).sum_comp
    (fun z : Fin (blockPrefix q k) => orderedBlockSamplesEquiv m q Real x (Fin.castLE (blockPrefix_mono q hk) z))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  rw [orderedBlockEquiv_cast_prefix m k q hk i v]
  exact orderedBlockSamplesEquiv_apply_component m q x (Fin.castLE hk i) v

def blockSums (m : Nat) (q : Nat → Nat) (x : (i : Fin m) → Fin (q i) → Real) : Fin m → Real :=
  fun i => ∑ v, x i v

theorem blockSums_partialSum (m k : Nat) (q : Nat → Nat) (hk : k ≤ m)
    (x : (i : Fin m) → Fin (q i) → Real) :
    FiniteWalk.partialSum k (blockSums m q x) =
      FiniteWalk.partialSum (blockPrefix q k) (orderedBlockSamplesEquiv m q Real x) := by
  rw [ordered_block_partial_sum m k q hk, partialSum_eq_sum_fin m k hk]
  rfl

#print axioms ordered_block_partial_sum
#print axioms blockSums_partialSum
end ConditionalSpectralExtremes.IIDRegroup
