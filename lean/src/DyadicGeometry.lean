import DyadicGrouping

/-! Geometric width properties of the corrected executable grouping.
The adjacent ratio is in fact at most four, hence also at most the five
used by the manuscript. These are properties of the recursively computed
integer groups, not assumptions about a chosen partition. -/

namespace ConditionalSpectralAudit.DyadicGrouping

theorem dyadic_groups_nonempty (M v : ℕ) (hv : 0 < v) (hlo : 2*v ≤ M) :
    dyadicGroups M v ≠ [] := by
  intro hnil
  have hh := (dyadic_groups_invariants M v hv hlo).1
  rw [hnil, List.sum_nil] at hh
  omega

theorem dyadic_groups_boundary_bounds (M v : ℕ) (hv : 0 < v) (hlo : 2*v ≤ M) :
    (∀ w ∈ (dyadicGroups M v).head?, v ≤ w ∧ w ≤ 2*v) ∧
      (∀ w ∈ (dyadicGroups M v).getLast?, v ≤ w ∧ w ≤ 2*v) := by
  by_cases hstep : 0 < v ∧ 6*v ≤ M
  · rw [dyadicGroups, dif_pos hstep]
    constructor
    · intro w hw
      simp only [List.head?_cons, Option.mem_some_iff] at hw
      subst w
      omega
    · intro w hw
      rw [← List.cons_append, List.getLast?_concat] at hw
      simp only [Option.mem_some_iff] at hw
      subst w
      omega
  · have ht := terminal_split_correct M v hv hlo (by omega)
    rw [dyadicGroups, dif_neg hstep]
    exact ⟨fun w hw => ht.2.2.2 w (List.mem_of_mem_head? hw),
      fun w hw => ht.2.2.2 w (List.mem_of_mem_getLast? hw)⟩

theorem dyadic_groups_boundary_exact (M v : ℕ) (hv : 0 < v) (hstep : 6*v ≤ M) :
    (dyadicGroups M v).head? = some v ∧ (dyadicGroups M v).getLast? = some v := by
  rw [dyadicGroups, dif_pos ⟨hv, hstep⟩]
  constructor
  · rfl
  · rw [← List.cons_append, List.getLast?_concat]

def adjacentComparable (x y : ℕ) : Prop := x ≤ 4*y ∧ y ≤ 4*x

theorem chain_of_width_bounds (l : List ℕ) (v : ℕ)
    (hb : ∀ x ∈ l, v ≤ x ∧ x ≤ 2*v) : l.IsChain adjacentComparable := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons x l ih =>
    have hh := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    apply hh.cons
    intro y hy
    have hx := hb x List.mem_cons_self
    have hy' := hb y (List.mem_cons_of_mem x (List.mem_of_mem_head? hy))
    unfold adjacentComparable
    constructor <;> omega

theorem dyadic_groups_adjacent (M v : ℕ) (hv : 0 < v) (hlo : 2*v ≤ M) :
    (dyadicGroups M v).IsChain adjacentComparable := by
  induction M using Nat.strong_induction_on generalizing v with
  | h M ih =>
    by_cases hstep : 0 < v ∧ 6*v ≤ M
    · have hr := dyadic_step_preserves_remaining M v hv hstep.2
      have hd := dyadic_step_decreases M v hv hstep.2
      have hchain := ih (M-2*v) hd (2*v) hr.1 hr.2
      have hb := dyadic_groups_boundary_bounds (M-2*v) (2*v) hr.1 hr.2
      have hne := dyadic_groups_nonempty (M-2*v) (2*v) hr.1 hr.2
      rw [dyadicGroups, dif_pos hstep]
      have happend : (dyadicGroups (M-2*v) (2*v) ++ [v]).IsChain adjacentComparable := by
        apply hchain.append (List.IsChain.singleton v)
        intro x hx y hy
        simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst y
        have hx' := hb.2 x hx
        unfold adjacentComparable
        constructor <;> omega
      apply happend.cons
      intro y hy
      rw [List.head?_append_of_ne_nil _ hne] at hy
      have hy' := hb.1 y hy
      unfold adjacentComparable
      constructor <;> omega
    · have ht := terminal_split_correct M v hv hlo (by omega)
      rw [dyadicGroups, dif_neg hstep]
      exact chain_of_width_bounds _ v ht.2.2.2

theorem dyadic_groups_adjacent_five (M v : ℕ) (hv : 0 < v) (hlo : 2*v ≤ M) :
    (dyadicGroups M v).IsChain (fun x y => x ≤ 5*y ∧ y ≤ 5*x) := by
  apply (dyadic_groups_adjacent M v hv hlo).imp
  intro x y hxy
  unfold adjacentComparable at hxy
  constructor <;> omega

#print axioms dyadic_groups_nonempty
#print axioms dyadic_groups_boundary_bounds
#print axioms dyadic_groups_boundary_exact
#print axioms chain_of_width_bounds
#print axioms dyadic_groups_adjacent
#print axioms dyadic_groups_adjacent_five

end ConditionalSpectralAudit.DyadicGrouping
