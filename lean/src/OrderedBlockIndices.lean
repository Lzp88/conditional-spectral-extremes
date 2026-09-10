import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

/-! An explicit ordered equivalence between variable length blocks and
a single finite interval. Its value is exactly prefix length plus offset. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup

def blockPrefix (q : Nat → Nat) (i : Nat) : Nat := ∑ j ∈ Finset.range i, q j

theorem blockPrefix_step (q : Nat → Nat) (i : Nat) :
    blockPrefix q (i+1)=blockPrefix q i+q i := Finset.sum_range_succ q i

theorem blockPrefix_mono (q : Nat → Nat) : Monotone (blockPrefix q) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [blockPrefix_step]
  omega

def blockIndex (m : Nat) (q : Nat → Nat) (a : (i : Fin m) × Fin (q i)) : Fin (blockPrefix q m) :=
  ⟨blockPrefix q a.1+a.2, lt_of_lt_of_le
    (by rw [blockPrefix_step]; exact Nat.add_lt_add_left a.2.isLt _)
    (blockPrefix_mono q (Nat.succ_le_of_lt a.1.isLt))⟩

theorem blockIndex_strict_order (m : Nat) (q : Nat → Nat) (a b : (i : Fin m) × Fin (q i))
    (hab : a.1 < b.1) : (blockIndex m q a).val < (blockIndex m q b).val := by
  have hlt : blockPrefix q a.1+a.2 < blockPrefix q (a.1+1) := by
    rw [blockPrefix_step]
    exact Nat.add_lt_add_left a.2.isLt _
  have hle := blockPrefix_mono q (Nat.succ_le_of_lt hab)
  simp only [Nat.succ_eq_add_one] at hle
  change blockPrefix q a.1+a.2 < blockPrefix q b.1+b.2
  omega

theorem blockIndex_injective (m : Nat) (q : Nat → Nat) : Function.Injective (blockIndex m q) := by
  intro a b he
  have hv := congrArg Fin.val he
  have hi : a.1=b.1 := by
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · have hh := blockIndex_strict_order m q a b h
      omega
    · exact h
    · have hh := blockIndex_strict_order m q b a h
      omega
  rcases a with ⟨i,v⟩
  rcases b with ⟨j,w⟩
  dsimp at hi
  subst j
  have hvw : v=w := by
    apply Fin.ext
    change blockPrefix q i+v.val=blockPrefix q i+w.val at hv
    omega
  subst w
  rfl

def orderedBlockEquiv (m : Nat) (q : Nat → Nat) : ((i : Fin m) × Fin (q i)) ≃ Fin (blockPrefix q m) :=
  Equiv.ofBijective (blockIndex m q) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blockIndex_injective m q, by simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range, blockPrefix]⟩)

theorem orderedBlockEquiv_apply_val (m : Nat) (q : Nat → Nat) (i : Fin m) (v : Fin (q i)) :
    (orderedBlockEquiv m q ⟨i,v⟩).val=blockPrefix q i+v.val := rfl

#print axioms blockIndex_injective
#print axioms orderedBlockEquiv_apply_val
end ConditionalSpectralExtremes.IIDRegroup
