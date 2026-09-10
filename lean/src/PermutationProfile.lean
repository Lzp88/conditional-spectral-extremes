import ManuscriptDefinitions
import Mathlib.GroupTheory.Perm.Centralizer

/-! The literal cycle profile of a permutation, including fixed points.
Its size constraint is proved from the actual permutation partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem positive_multiset_card_le_sum (m : Multiset Nat) (hm : ∀ a ∈ m, 0 < a) :
    m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha := hm a (by simp)
    have hh := ih (fun b hb => hm b (by simp [hb]))
    simpa only [Multiset.card_cons,Multiset.sum_cons] using (by omega : m.card+1 ≤ a+m.sum)

def partitionConfiguration {n : Nat} (p : Nat.Partition n) : Configuration n :=
  fun j => ⟨p.parts.count (j.val+1),by
    have hh := (Multiset.count_le_card (j.val+1) p.parts).trans
      (positive_multiset_card_le_sum p.parts (fun _ hi => p.parts_pos hi))
    rw [p.parts_sum] at hh
    omega⟩

def profileParts {n : Nat} (c : Configuration n) : Multiset Nat :=
  ∑ j : Fin n, Multiset.replicate (c j).val (j.val+1)

theorem profileParts_count {n : Nat} (c : Configuration n) (j : Fin n) :
    (profileParts c).count (j.val+1)=(c j).val := by
  classical
  unfold profileParts
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate,Nat.add_right_cancel_iff,Fin.val_inj]
  simp

theorem profileParts_mem {n : Nat} (c : Configuration n) {a : Nat}
    (ha : a ∈ profileParts c) : 0 < a ∧ a ≤ n := by
  obtain ⟨j,_,hj⟩ := Multiset.mem_sum.mp ha
  have hh : a=j.val+1 := Multiset.eq_of_mem_replicate hj
  rw [hh]
  omega

theorem profileParts_sum {n : Nat} (c : Configuration n) : (profileParts c).sum=totalSize c := by
  unfold profileParts totalSize
  rw [Multiset.sum_sum]
  simp only [Multiset.sum_replicate,smul_eq_mul,mul_comm]

theorem profileParts_card {n : Nat} (c : Configuration n) : (profileParts c).card=cycleCount c := by
  unfold profileParts cycleCount
  rw [Multiset.card_sum]
  simp only [Multiset.card_replicate]

theorem profileParts_partitionConfiguration {n : Nat} (p : Nat.Partition n) :
    profileParts (partitionConfiguration p)=p.parts := by
  classical
  apply Multiset.ext.mpr
  intro a
  by_cases ha : 0 < a ∧ a ≤ n
  · let j : Fin n := ⟨a-1,by omega⟩
    have hj : j.val+1=a := by dsimp [j]; omega
    rw [← hj,profileParts_count]
    rfl
  · have hleft : a ∉ profileParts (partitionConfiguration p) := fun hh => ha (profileParts_mem _ hh)
    have hright : a ∉ p.parts := fun hh => ha ⟨p.parts_pos hh,p.le_of_mem_parts hh⟩
    simp only [Multiset.count_eq_zero.mpr hleft,Multiset.count_eq_zero.mpr hright]

theorem partitionConfiguration_size {n : Nat} (p : Nat.Partition n) :
    totalSize (partitionConfiguration p)=n := by
  rw [← profileParts_sum,profileParts_partitionConfiguration,p.parts_sum]

theorem partitionConfiguration_count {n : Nat} (p : Nat.Partition n) :
    cycleCount (partitionConfiguration p)=p.parts.card := by
  rw [← profileParts_card,profileParts_partitionConfiguration]

def permutationConfiguration {n : Nat} (σ : Equiv.Perm (Fin n)) : Configuration n :=
  partitionConfiguration ⟨σ.partition.parts,σ.partition.parts_pos,
    by simpa only [Fintype.card_fin] using σ.partition.parts_sum⟩

theorem permutationConfiguration_parts {n : Nat} (σ : Equiv.Perm (Fin n)) :
    profileParts (permutationConfiguration σ)=σ.partition.parts :=
  profileParts_partitionConfiguration _

theorem permutationConfiguration_size {n : Nat} (σ : Equiv.Perm (Fin n)) :
    totalSize (permutationConfiguration σ)=n := partitionConfiguration_size _

theorem permutationConfiguration_count {n : Nat} (σ : Equiv.Perm (Fin n)) :
    cycleCount (permutationConfiguration σ)=σ.partition.parts.card := partitionConfiguration_count _

#print axioms permutationConfiguration_parts
#print axioms permutationConfiguration_size
end ConditionalSpectralExtremes
