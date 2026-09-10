import MatchingConjugacy
import MatchingComponentProfile

/-! Simultaneous relabeling preserves the literal connected-component
profile of an arbitrary fixed matching and its partner. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {α : Type*}

def matchingGraphConjugationIso (g : Perm α) (a b : Matching α) :
    matchingGraph a b ≃g matchingGraph (conjugateMatching g a) (conjugateMatching g b) where
  toEquiv := g
  map_rel_iff' := by
    intro x y
    change (g*a.val*g⁻¹) (g x)=g y ∨ (g*b.val*g⁻¹) (g x)=g y ↔
      a.val x=y ∨ b.val x=y
    simp

def twoMatchingParts [Fintype α] (a b : Matching α) : Multiset Nat :=
  ∑ C : (matchingGraph a b).ConnectedComponent,
    {Nat.card (GraphComponentFiber (matchingGraph a b) C) / 2}

theorem matchingGraphIso_fiber_card {β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (e : G ≃g H) (C : G.ConnectedComponent) :
    Nat.card (GraphComponentFiber G C)=Nat.card (GraphComponentFiber H (e.connectedComponentEquiv C)) := by
  exact Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp e C)

theorem twoMatchingParts_conjugation [Fintype α] (g : Perm α) (a b : Matching α) :
    twoMatchingParts (conjugateMatching g a) (conjugateMatching g b)=twoMatchingParts a b := by
  let e := matchingGraphConjugationIso g a b
  unfold twoMatchingParts
  rw [← Equiv.sum_comp e.connectedComponentEquiv
    (fun C => ({Nat.card (GraphComponentFiber _ C) / 2} : Multiset Nat))]
  apply Finset.sum_congr rfl
  intro C _
  rw [← matchingGraphIso_fiber_card _ _ e C]

theorem twoMatchingParts_standard {ι : Type*} [Fintype ι] (b : Matching (ι × Bool)) :
    twoMatchingParts (standardMatching ι) b=matchingComponentParts b := by
  unfold twoMatchingParts matchingComponentParts
  congr 1
  ext C
  simp only [Finset.mem_univ]

theorem twoMatchingParts_partition {n : Nat} (a b : Matching (Fin n × Bool)) :
    ∃ p : Nat.Partition n, p.parts=twoMatchingParts a b := by
  obtain ⟨g,rfl⟩ := conjugateMatching_surjective (standardMatching (Fin n)) a
  let b' := conjugateMatching g⁻¹ b
  have hb : conjugateMatching g b'=b := by
    dsimp only [b']
    rw [← conjugateMatching_mul, mul_inv_cancel, conjugateMatching_one]
  let hp := matchingComponentPartition b'
  refine ⟨⟨hp.parts,hp.parts_pos,by simpa only [Fintype.card_fin] using hp.parts_sum⟩,?_⟩
  change matchingComponentParts b'=twoMatchingParts _ b
  rw [← hb, twoMatchingParts_conjugation, twoMatchingParts_standard]

def twoMatchingConfiguration {n : Nat} (a b : Matching (Fin n × Bool)) : Configuration n :=
  partitionConfiguration (twoMatchingParts_partition a b).choose

theorem twoMatchingConfiguration_parts {n : Nat} (a b : Matching (Fin n × Bool)) :
    profileParts (twoMatchingConfiguration a b)=twoMatchingParts a b := by
  rw [twoMatchingConfiguration, profileParts_partitionConfiguration]
  exact (twoMatchingParts_partition a b).choose_spec

theorem twoMatchingConfiguration_size {n : Nat} (a b : Matching (Fin n × Bool)) :
    totalSize (twoMatchingConfiguration a b)=n := partitionConfiguration_size _

theorem profileParts_injective {n : Nat} : Function.Injective (@profileParts n) := by
  intro c d h
  funext j
  apply Fin.ext
  rw [← profileParts_count c j, ← profileParts_count d j, h]

theorem twoMatchingConfiguration_standard {n : Nat} (b : Matching (Fin n × Bool)) :
    twoMatchingConfiguration (standardMatching (Fin n)) b=matchingConfiguration b := by
  apply profileParts_injective
  rw [twoMatchingConfiguration_parts, twoMatchingParts_standard, matchingConfiguration_parts]

theorem twoMatchingConfiguration_conjugation {n : Nat} (g : Perm (Fin n × Bool))
    (a b : Matching (Fin n × Bool)) :
    twoMatchingConfiguration (conjugateMatching g a) (conjugateMatching g b)=
      twoMatchingConfiguration a b := by
  apply profileParts_injective
  rw [twoMatchingConfiguration_parts, twoMatchingConfiguration_parts, twoMatchingParts_conjugation]

#print axioms matchingGraphConjugationIso
#print axioms twoMatchingParts_conjugation
#print axioms twoMatchingConfiguration_parts
#print axioms twoMatchingConfiguration_conjugation
end ConditionalSpectralExtremes.TwoMatchings
