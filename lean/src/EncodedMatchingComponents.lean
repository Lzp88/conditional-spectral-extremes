import EncodedMatching
import PermutationOrbitLabels

/-! The encoding preserves the actual graph components, with two graph
vertices for each index in the corresponding permutation orbit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*}

theorem encoded_adj_sameCycle (π : Perm ι) (bits : ι → Bool) {x y : ι × Bool}
    (h : (matchingGraph (standardMatching ι) (encodedMatching π bits)).Adj x y) :
    π.SameCycle x.1 y.1 := by
  rcases h with h | h
  · rw [← h]
    exact Perm.SameCycle.refl _ _
  · rw [← h, encodedMatching_apply]
    rcases orientation_cases bits x with hx | hx
    · rw [hx, encodedPartner_out]
      exact Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _)
    · rw [hx, encodedPartner_in]
      exact Perm.sameCycle_symm_apply_right.mpr (Perm.SameCycle.refl _ _)

theorem encoded_reachable_sameCycle (π : Perm ι) (bits : ι → Bool) {x y : ι × Bool}
    (h : (matchingGraph (standardMatching ι) (encodedMatching π bits)).Reachable x y) :
    π.SameCycle x.1 y.1 := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact Perm.SameCycle.refl _ _
  | cons h p ih => exact (encoded_adj_sameCycle π bits h).trans ih

theorem encoded_product_pow_out (π : Perm ι) (bits : ι → Bool) (i : ι) (k : Nat) :
    (((standardMatching ι).val * (encodedMatching π bits).val)^k) (orientationOut bits i) =
      orientationOut bits ((π^k) i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, encoded_product_out, pow_succ', Perm.mul_apply]

theorem encoded_reachable_out (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    (matchingGraph (standardMatching ι) (encodedMatching π bits)).Reachable x
      (orientationOut bits x.1) := by
  rcases orientation_cases bits x with hx | hx
  · exact hx ▸ SimpleGraph.Reachable.refl _
  · have hh := (matchingGraph_adj_a (standardMatching ι) (encodedMatching π bits) x).reachable
    convert hh using 1
    rw [hx]
    simp [standardMatching_apply, orientationIn, orientationOut]

theorem encoded_graph_reachable_iff [Finite ι] (π : Perm ι) (bits : ι → Bool) (x y : ι × Bool) :
    (matchingGraph (standardMatching ι) (encodedMatching π bits)).Reachable x y ↔
      π.SameCycle x.1 y.1 := by
  refine ⟨encoded_reachable_sameCycle π bits, ?_⟩
  intro h
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hh := matchingGraph_reachable_pow (standardMatching ι) (encodedMatching π bits)
    (orientationOut bits x.1) k
  rw [encoded_product_pow_out, hk] at hh
  exact (encoded_reachable_out π bits x).trans (hh.trans (encoded_reachable_out π bits y).symm)

def encodedComponentOrbit [Finite ι] (π : Perm ι) (bits : ι → Bool) :
    (matchingGraph (standardMatching ι) (encodedMatching π bits)).ConnectedComponent →
      PermutationOrbit π :=
  Quot.lift (fun x => permutationOrbitClass π x.1)
    (fun _ _ h => Quotient.sound (encoded_reachable_sameCycle π bits h))

def encodedComponentEquiv [Finite ι] (π : Perm ι) (bits : ι → Bool) :
    (matchingGraph (standardMatching ι) (encodedMatching π bits)).ConnectedComponent ≃
      PermutationOrbit π where
  toFun := encodedComponentOrbit π bits
  invFun := Quotient.lift (fun i =>
    (matchingGraph (standardMatching ι) (encodedMatching π bits)).connectedComponentMk
      (orientationOut bits i)) (by
        intro i j h
        exact Quot.sound ((encoded_graph_reachable_iff π bits _ _).mpr h))
  left_inv C := by
    induction C using Quot.inductionOn with | h x =>
      exact Quot.sound (encoded_reachable_out π bits x).symm
  right_inv q := by
    induction q using Quotient.inductionOn with | h i => rfl

theorem encodedComponentEquiv_class [Finite ι] (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    encodedComponentEquiv π bits
      ((matchingGraph (standardMatching ι) (encodedMatching π bits)).connectedComponentMk x) =
        permutationOrbitClass π x.1 := rfl

abbrev GraphComponentFiber {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) :=
  {x : V // G.connectedComponentMk x=C}

def encodedComponentFiberEquiv [Finite ι] (π : Perm ι) (bits : ι → Bool)
    (C : (matchingGraph (standardMatching ι) (encodedMatching π bits)).ConnectedComponent) :
    GraphComponentFiber (matchingGraph (standardMatching ι) (encodedMatching π bits)) C ≃
      PermutationOrbitFiber π (encodedComponentEquiv π bits C) × Bool where
  toFun x := (⟨x.val.1, by
    rw [← encodedComponentEquiv_class π bits x.val, x.property]⟩, x.val.2)
  invFun y := ⟨(y.1.val,y.2), by
    apply (encodedComponentEquiv π bits).injective
    rw [encodedComponentEquiv_class]
    exact y.1.property⟩
  left_inv x := rfl
  right_inv y := rfl

theorem encodedComponentFiber_card [Finite ι] (π : Perm ι) (bits : ι → Bool)
    (C : (matchingGraph (standardMatching ι) (encodedMatching π bits)).ConnectedComponent) :
    Nat.card (GraphComponentFiber (matchingGraph (standardMatching ι) (encodedMatching π bits)) C) =
      2 * Nat.card (PermutationOrbitFiber π (encodedComponentEquiv π bits C)) := by
  rw [Nat.card_congr (encodedComponentFiberEquiv π bits C), Nat.card_prod]
  rw [show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card], mul_comm]

#print axioms encoded_graph_reachable_iff
#print axioms encodedComponentEquiv
#print axioms encodedComponentFiber_card
end ConditionalSpectralExtremes.TwoMatchings
