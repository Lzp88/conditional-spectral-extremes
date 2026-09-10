import MatchingGraphComponents
import BinaryGraphColorings

/-! A genuine binary coloring of every finite union of two fixed-point-free
involutions. The exact number of colorings is two to the actual number of
graph components; bipartiteness is proved, not assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {α : Type*}

theorem matching_cycle_membership_flip_a (a b : Matching α) (r x : α)
    (hc : AlternatingConnected a b r x) :
    (a.val*b.val).SameCycle r (a.val x) ↔ ¬(a.val*b.val).SameCycle r x := by
  constructor
  · intro hax hx
    exact matching_cycles_distinct a b x (hx.symm.trans hax)
  · intro hx
    have hh := (matching_cycle_reflection a b (a.val r) x).mpr (hc.resolve_left hx)
    rwa [matching_apply_twice] at hh

theorem matching_partners_sameCycle (a b : Matching α) (x : α) :
    (a.val*b.val).SameCycle (a.val x) (b.val x) := by
  refine ⟨-1, ?_⟩
  simp only [zpow_neg_one, mul_inv_rev, matching_inv, Perm.mul_apply, matching_apply_twice]

theorem matching_cycle_membership_flip_b (a b : Matching α) (r x : α)
    (hc : AlternatingConnected a b r x) :
    (a.val*b.val).SameCycle r (b.val x) ↔ ¬(a.val*b.val).SameCycle r x := by
  have hh : (a.val*b.val).SameCycle r (b.val x) ↔ (a.val*b.val).SameCycle r (a.val x) :=
    ⟨fun h => h.trans (matching_partners_sameCycle a b x).symm,
      fun h => h.trans (matching_partners_sameCycle a b x)⟩
  exact hh.trans (matching_cycle_membership_flip_a a b r x hc)

def matchingBaseColor [Finite α] (a b : Matching α) (x : α) : Bool :=
  decide ((a.val*b.val).SameCycle
    (graphComponentRoot (matchingGraph a b) ((matchingGraph a b).connectedComponentMk x)) x)

theorem matchingBaseColor_a [Finite α] (a b : Matching α) (x : α) :
    matchingBaseColor a b (a.val x) = !(matchingBaseColor a b x) := by
  unfold matchingBaseColor
  rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (matchingGraph_adj_a a b x)]
  rw [matching_cycle_membership_flip_a a b _ x
    ((matchingGraph_reachable_iff a b _ x).mp (graphComponentRoot_reachable (matchingGraph a b) x))]
  by_cases h : (a.val*b.val).SameCycle
      (graphComponentRoot (matchingGraph a b) ((matchingGraph a b).connectedComponentMk x)) x <;>
    simp [h]

theorem matchingBaseColor_b [Finite α] (a b : Matching α) (x : α) :
    matchingBaseColor a b (b.val x) = !(matchingBaseColor a b x) := by
  unfold matchingBaseColor
  rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (matchingGraph_adj_b a b x)]
  rw [matching_cycle_membership_flip_b a b _ x
    ((matchingGraph_reachable_iff a b _ x).mp (graphComponentRoot_reachable (matchingGraph a b) x))]
  by_cases h : (a.val*b.val).SameCycle
      (graphComponentRoot (matchingGraph a b) ((matchingGraph a b).connectedComponentMk x)) x <;>
    simp [h]

def matchingBinaryColoring [Finite α] (a b : Matching α) : BinaryColoring (matchingGraph a b) :=
  ⟨matchingBaseColor a b, by
    intro x y h
    rcases h with h | h
    · subst y
      rw [matchingBaseColor_a, Bool.not_not]
    · subst y
      rw [matchingBaseColor_b, Bool.not_not]⟩

def componentNumber (a b : Matching α) : ℕ := Nat.card (matchingGraph a b).ConnectedComponent

theorem actual_matching_coloring_count [Fintype α] (a b : Matching α) :
    Nat.card (BinaryColoring (matchingGraph a b)) = 2 ^ componentNumber a b :=
  binaryColoring_card (matchingGraph a b) (matchingBinaryColoring a b)

#print axioms matching_cycle_membership_flip_a
#print axioms matching_cycle_membership_flip_b
#print axioms matchingBaseColor_a
#print axioms matchingBaseColor_b
#print axioms matchingBinaryColoring
#print axioms actual_matching_coloring_count
end ConditionalSpectralExtremes.TwoMatchings
