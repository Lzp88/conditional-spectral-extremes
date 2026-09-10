import Mathlib

/-! Given one genuine binary graph coloring, every other coloring is obtained
by an independent flip on each actual connected component. This is an exact
finite equivalence, used to count orientations of matching components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
variable {V : Type*}

abbrev BinaryColoring (G : SimpleGraph V) :=
  {c : V → Bool // ∀ ⦃x y⦄, G.Adj x y → c x = !(c y)}

def graphComponentRoot (G : SimpleGraph V) (C : G.ConnectedComponent) : V :=
  C.nonempty_supp.choose

theorem graphComponentRoot_spec (G : SimpleGraph V) (C : G.ConnectedComponent) :
    G.connectedComponentMk (graphComponentRoot G C) = C := C.nonempty_supp.choose_spec

theorem graphComponentRoot_reachable (G : SimpleGraph V) (x : V) :
    G.Reachable (graphComponentRoot G (G.connectedComponentMk x)) x :=
  SimpleGraph.ConnectedComponent.exact (graphComponentRoot_spec G _)

theorem binaryColoring_difference_adj {G : SimpleGraph V} (c d : BinaryColoring G)
    {x y : V} (h : G.Adj x y) : Bool.xor (c.val x) (d.val x) = Bool.xor (c.val y) (d.val y) := by
  rw [c.property h, d.property h]
  cases c.val y <;> cases d.val y <;> rfl

theorem binaryColoring_difference_reachable {G : SimpleGraph V} (c d : BinaryColoring G)
    {x y : V} (h : G.Reachable x y) : Bool.xor (c.val x) (d.val x) = Bool.xor (c.val y) (d.val y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (binaryColoring_difference_adj c d h).trans ih

def binaryColoringEquiv (G : SimpleGraph V) (d : BinaryColoring G) :
    BinaryColoring G ≃ (G.ConnectedComponent → Bool) where
  toFun c C := Bool.xor (c.val (graphComponentRoot G C)) (d.val (graphComponentRoot G C))
  invFun f := ⟨fun x => Bool.xor (f (G.connectedComponentMk x)) (d.val x), by
    intro x y h
    change Bool.xor (f (G.connectedComponentMk x)) (d.val x) =
      !(Bool.xor (f (G.connectedComponentMk y)) (d.val y))
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h, d.property h]
    cases f (G.connectedComponentMk y) <;> cases d.val y <;> rfl⟩
  left_inv c := by
    apply Subtype.ext
    funext x
    have hh := binaryColoring_difference_reachable c d (graphComponentRoot_reachable G x)
    change Bool.xor (Bool.xor (c.val (graphComponentRoot G (G.connectedComponentMk x)))
      (d.val (graphComponentRoot G (G.connectedComponentMk x)))) (d.val x) = c.val x
    rw [hh]
    cases c.val x <;> cases d.val x <;> rfl
  right_inv f := by
    funext C
    change Bool.xor (Bool.xor (f (G.connectedComponentMk (graphComponentRoot G C)))
      (d.val (graphComponentRoot G C))) (d.val (graphComponentRoot G C)) = f C
    rw [graphComponentRoot_spec]
    cases f C <;> cases d.val (graphComponentRoot G C) <;> rfl

theorem binaryColoring_card [Fintype V] (G : SimpleGraph V) (d : BinaryColoring G) :
    Nat.card (BinaryColoring G) = 2 ^ Nat.card G.ConnectedComponent := by
  let _ : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let _ : Fintype (BinaryColoring G) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool] using
    Fintype.card_congr (binaryColoringEquiv G d)

#print axioms binaryColoring_difference_reachable
#print axioms binaryColoringEquiv
#print axioms binaryColoring_card
end ConditionalSpectralExtremes.TwoMatchings
