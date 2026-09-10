import PermutationProfile

/-! The profile weight is the reciprocal of the genuine cycle-centralizer
denominator. This is finite enumeration algebra, not an assumed Ewens law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes

def profileDenominator {n : Nat} (c : Configuration n) : Nat :=
  ∏ j : Fin n, (j.val+1)^(c j).val * (c j).val.factorial

def multiplicityFactorials (m : Multiset Nat) : Nat :=
  ∏ j ∈ m.toFinset, (m.count j).factorial

theorem profileWeight_eq_inv_denominator {n : Nat} (c : Configuration n) :
    profileWeight c=(profileDenominator c : Real)⁻¹ := by
  unfold profileWeight profileDenominator
  push_cast
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [mul_inv_rev,inv_pow,div_eq_mul_inv]
  ring

theorem prod_positive_lengths {M : Type*} [CommMonoid M] (n : Nat) (f : Nat → M) :
    (∏ j : Fin n, f (j.val+1))=∏ j ∈ Finset.Ico 1 (n+1), f j := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j+1)) n,Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel,add_comm]

theorem partition_denominator (n : Nat) (m : Multiset Nat)
    (hm : ∀ j ∈ m, 0 < j ∧ j ≤ n) :
    (∏ j : Fin n, (j.val+1)^(m.count (j.val+1))*(m.count (j.val+1)).factorial)=
      m.prod*multiplicityFactorials m := by
  have hsub : m.toFinset ⊆ Finset.Ico 1 (n+1) := by
    intro j hj
    have hh := hm j (Multiset.mem_toFinset.mp hj)
    simp only [Finset.mem_Ico]
    omega
  rw [prod_positive_lengths n (fun j => j^(m.count j)*(m.count j).factorial),
    Finset.prod_mul_distrib,← Finset.prod_multiset_count_of_subset m _ hsub]
  congr 1
  symm
  apply Finset.prod_subset hsub
  intro j _ hj
  have hh : m.count j=0 := Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hj)
  rw [hh,Nat.factorial_zero]

theorem profileDenominator_parts {n : Nat} (c : Configuration n) :
    profileDenominator c=(profileParts c).prod*multiplicityFactorials (profileParts c) := by
  have hh := partition_denominator n (profileParts c) (fun _ hj => profileParts_mem c hj)
  simpa only [profileParts_count,profileDenominator] using hh

theorem multiplicityFactorials_add_ones (m : Multiset Nat) (hm : 1 ∉ m) (f : Nat) :
    multiplicityFactorials (m+Multiset.replicate f 1)=f.factorial*multiplicityFactorials m := by
  classical
  by_cases hf : f=0
  · simp [hf,multiplicityFactorials]
  have hfin : (Multiset.replicate f 1).toFinset={1} := by
    ext j
    simp only [Multiset.mem_toFinset,Multiset.mem_replicate,Finset.mem_singleton]
    simp [hf]
  unfold multiplicityFactorials
  rw [Multiset.toFinset_add,hfin,Finset.prod_union (by simpa using hm)]
  have hprod : (∏ j ∈ m.toFinset, ((m+Multiset.replicate f 1).count j).factorial)=
      ∏ j ∈ m.toFinset, (m.count j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    have hj1 : 1 ≠ j := by intro hh; apply hm; simpa only [hh] using Multiset.mem_toFinset.mp hj
    simp only [Multiset.count_add,Multiset.count_replicate,if_neg hj1,add_zero]
  rw [hprod]
  simp only [Finset.prod_singleton,Multiset.count_add,Multiset.count_eq_zero.mpr hm,
    Multiset.count_replicate_self,zero_add]
  exact mul_comm _ _

theorem permutation_profile_denominator {n : Nat} (σ : Equiv.Perm (Fin n)) :
    profileDenominator (permutationConfiguration σ)=
      (n-σ.cycleType.sum).factorial*σ.cycleType.prod*
        (∏ j ∈ σ.cycleType.toFinset, (σ.cycleType.count j).factorial) := by
  rw [profileDenominator_parts,permutationConfiguration_parts,Equiv.Perm.parts_partition]
  have hnone : 1 ∉ σ.cycleType := by
    intro h
    have hh := Equiv.Perm.two_le_of_mem_cycleType h
    omega
  rw [Multiset.prod_add,Multiset.prod_replicate,one_pow,mul_one,
    multiplicityFactorials_add_ones σ.cycleType hnone]
  simp only [Fintype.card_fin,← Equiv.Perm.sum_cycleType,multiplicityFactorials]
  ring

#print axioms profileWeight_eq_inv_denominator
#print axioms permutation_profile_denominator
end ConditionalSpectralExtremes
