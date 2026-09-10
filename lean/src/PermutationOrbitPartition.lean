import PermutationOrbitLabels

/-! The multiset of sizes of all genuine SameCycle quotient fibers is
exactly the standard permutation partition, including one-cycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Equiv Set
open scoped BigOperators
namespace ConditionalSpectralExtremes
variable {α : Type*} [Fintype α] [DecidableEq α]

def permutationLabelFiberCard (σ : Perm α) (l : PermutationCycleLabels σ) : Nat :=
  Nat.card {x : α // permutationCycleLabel σ x=l}

theorem permutationOrbitFiber_card_label (σ : Perm α) (q : PermutationOrbit σ) :
    Nat.card (PermutationOrbitFiber σ q)=permutationLabelFiberCard σ (permutationOrbitLabelEquiv σ q) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  constructor
  · intro h
    rw [← h,permutationOrbitLabelEquiv_class]
  · intro h
    apply (permutationOrbitLabelEquiv σ).injective
    rwa [permutationOrbitLabelEquiv_class]

theorem permutationLabelFiberCard_inl (σ : Perm α) (c : ↑σ.cycleFactorsFinset) :
    permutationLabelFiberCard σ (Sum.inl c)=c.val.support.card := by
  have hh := Nat.card_congr (Equiv.subtypeEquivRight (fun x => permutationCycleLabel_inl_iff σ x c))
  simpa only [permutationLabelFiberCard,Nat.card_eq_fintype_card,Fintype.card_coe] using hh

theorem permutationLabelFiberCard_inr (σ : Perm α) (x : Function.fixedPoints σ) :
    permutationLabelFiberCard σ (Sum.inr x)=1 := by
  have hh := Nat.card_congr (Equiv.subtypeEquivRight (fun y => permutationCycleLabel_inr_iff σ y x))
  simpa only [permutationLabelFiberCard,Nat.card_eq_fintype_card,Fintype.card_subtype_eq] using hh

def permutationOrbitParts (σ : Perm α) : Multiset Nat :=
  ∑ q : PermutationOrbit σ, {Nat.card (PermutationOrbitFiber σ q)}

theorem permutationOrbitParts_eq_partition (σ : Perm α) :
    permutationOrbitParts σ=σ.partition.parts := by
  unfold permutationOrbitParts
  simp_rw [permutationOrbitFiber_card_label]
  rw [Equiv.sum_comp (permutationOrbitLabelEquiv σ)
    (fun l => ({permutationLabelFiberCard σ l} : Multiset Nat)),Fintype.sum_sum_type]
  simp_rw [permutationLabelFiberCard_inl,permutationLabelFiberCard_inr]
  rw [Finset.sum_const,Finset.card_univ,Multiset.nsmul_singleton,
    Perm.card_fixedPoints,Perm.sum_cycleType,Perm.parts_partition]
  congr 1
  rw [Finset.sum_coe_sort σ.cycleFactorsFinset (fun c => ({c.support.card} : Multiset Nat)),Perm.cycleType_def]
  change ((σ.cycleFactorsFinset.val.map (fun c => ({c.support.card} : Multiset Nat))).sum)=_
  simpa only [Multiset.map_map,Function.comp_def] using
    Multiset.sum_map_singleton (σ.cycleFactorsFinset.val.map (Finset.card ∘ Perm.support))

omit [Fintype α] [DecidableEq α] in
theorem permutationOrbitFiber_nonempty_partition (σ : Perm α) (q : PermutationOrbit σ) :
    Nonempty (PermutationOrbitFiber σ q) := by
  induction q using Quotient.inductionOn with
  | h x => exact ⟨⟨x,rfl⟩⟩

omit [DecidableEq α] in
theorem permutationOrbitFiber_card_pos (σ : Perm α) (q : PermutationOrbit σ) :
    0 < Nat.card (PermutationOrbitFiber σ q) := by
  let _ := permutationOrbitFiber_nonempty_partition σ q
  exact Nat.card_pos

theorem permutationOrbitParts_count (σ : Perm α) (j : Nat) :
    (σ.partition.parts).count j=
      ∑ q : PermutationOrbit σ, if Nat.card (PermutationOrbitFiber σ q)=j then 1 else 0 := by
  rw [← permutationOrbitParts_eq_partition,permutationOrbitParts,Multiset.count_sum']
  simp only [Multiset.count_singleton,eq_comm]

#print axioms permutationOrbitParts_eq_partition
#print axioms permutationOrbitParts_count
end ConditionalSpectralExtremes
