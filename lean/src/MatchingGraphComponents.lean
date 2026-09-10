import MatchingOrbitAlgebra

/-! The union of the two actual matching edge sets. Its genuine graph
components are exactly the two distinct equal-sized cycles of the product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv Set
variable {α : Type*}

def matchingGraph (a b : Matching α) : SimpleGraph α where
  Adj x y := a.val x = y ∨ b.val x = y
  symm := by
    constructor
    intro x y h
    rcases h with h | h
    · exact Or.inl (h ▸ matching_apply_twice a x)
    · exact Or.inr (h ▸ matching_apply_twice b x)
  loopless := by
    constructor
    intro x h
    rcases h with h | h
    · exact a.property.2 x h
    · exact b.property.2 x h

theorem matchingGraph_adj_a (a b : Matching α) (x : α) :
    (matchingGraph a b).Adj x (a.val x) := Or.inl rfl

theorem matchingGraph_adj_b (a b : Matching α) (x : α) :
    (matchingGraph a b).Adj x (b.val x) := Or.inr rfl

theorem matchingGraph_reachable_product (a b : Matching α) (x : α) :
    (matchingGraph a b).Reachable x ((a.val*b.val) x) :=
  (matchingGraph_adj_b a b x).reachable.trans (matchingGraph_adj_a a b (b.val x)).reachable

theorem matchingGraph_reachable_pow (a b : Matching α) (x : α) (k : ℕ) :
    (matchingGraph a b).Reachable x (((a.val*b.val)^k) x) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl x
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (matchingGraph_reachable_product a b _)

theorem matchingGraph_reachable_of_sameCycle [Finite α] (a b : Matching α) {x y : α}
    (h : (a.val*b.val).SameCycle x y) : (matchingGraph a b).Reachable x y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  exact matchingGraph_reachable_pow a b x k

theorem matchingGraph_reachable_iff [Finite α] (a b : Matching α) (x y : α) :
    (matchingGraph a b).Reachable x y ↔ AlternatingConnected a b x y := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact alternatingConnected_refl a b _
    | @cons x z y hxz p ih =>
      have hh : AlternatingConnected a b x z := by
        rcases hxz with hxz | hxz
        · rw [← hxz]
          exact alternatingConnected_a a b x
        · rw [← hxz]
          exact alternatingConnected_b a b x
      exact alternatingConnected_trans a b hh ih
  · rintro (h | h)
    · exact matchingGraph_reachable_of_sameCycle a b h
    · exact (matchingGraph_adj_a a b x).reachable.trans (matchingGraph_reachable_of_sameCycle a b h)

theorem matchingGraph_component_two_cycles [Finite α] (a b : Matching α) (x : α) :
    {y | (matchingGraph a b).Reachable x y} =
      {y | (a.val*b.val).SameCycle x y} ∪ {y | (a.val*b.val).SameCycle (a.val x) y} := by
  ext y
  exact matchingGraph_reachable_iff a b x y

theorem matchingGraph_component_card [Finite α] (a b : Matching α) (x : α) :
    Nat.card {y // (matchingGraph a b).Reachable x y} =
      2 * Nat.card {y // (a.val*b.val).SameCycle x y} := by
  let e := (Equiv.setCongr (matchingGraph_component_two_cycles a b x)).trans
    (Equiv.Set.union (alternating_component_two_disjoint_cycles a b x).2)
  have hh := Nat.card_congr e
  rw [Nat.card_sum] at hh
  have hh' : Nat.card {y // (matchingGraph a b).Reachable x y} =
      Nat.card {y // (a.val*b.val).SameCycle x y} +
        Nat.card {y // (a.val*b.val).SameCycle (a.val x) y} := by
    simpa only [Set.mem_ofPred_eq] using! hh
  rw [← Nat.card_congr (matchingCycleReflectionEquiv a b x)] at hh'
  simpa only [two_mul] using hh'

theorem product_isCycleOn_orbit (a b : Matching α) (x : α) :
    (a.val*b.val).IsCycleOn {y | (a.val*b.val).SameCycle x y} := by
  refine ⟨⟨?_, (a.val*b.val).injective.injOn, ?_⟩, ?_⟩
  · intro y hy
    exact Perm.sameCycle_apply_right.mpr hy
  · intro y hy
    refine ⟨(a.val*b.val).symm y, Perm.sameCycle_symm_apply_right.mpr hy, ?_⟩
    exact (a.val*b.val).apply_symm_apply y
  · intro y hy z hz
    exact hy.symm.trans hz

theorem actual_matching_component_two_equal_cycles [Finite α] (a b : Matching α) (x : α) :
    ∃ j : ℕ, 0 < j ∧
      Nat.card {y // (matchingGraph a b).Reachable x y} = 2*j ∧
      Nat.card {y // (a.val*b.val).SameCycle x y} = j ∧
      Nat.card {y // (a.val*b.val).SameCycle (a.val x) y} = j ∧
      (a.val*b.val).IsCycleOn {y | (a.val*b.val).SameCycle x y} ∧
      (a.val*b.val).IsCycleOn {y | (a.val*b.val).SameCycle (a.val x) y} := by
  refine ⟨Nat.card {y // (a.val*b.val).SameCycle x y}, ?_,
    matchingGraph_component_card a b x, rfl, (Nat.card_congr (matchingCycleReflectionEquiv a b x)).symm,
    product_isCycleOn_orbit a b x, product_isCycleOn_orbit a b (a.val x)⟩
  let _ : Nonempty {y // (a.val*b.val).SameCycle x y} := ⟨⟨x, Perm.SameCycle.refl _ _⟩⟩
  exact Nat.card_pos

#print axioms matchingGraph_reachable_iff
#print axioms matchingGraph_component_card
#print axioms product_isCycleOn_orbit
#print axioms actual_matching_component_two_equal_cycles
end ConditionalSpectralExtremes.TwoMatchings
