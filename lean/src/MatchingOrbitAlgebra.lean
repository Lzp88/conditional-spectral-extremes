import Mathlib

/-! Actual fixed-point-free involutions. The two cycles in an alternating
component are distinct: an identification would create a fixed point in
one of the two involutions, according to the parity of the connecting power. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {α : Type*}

abbrev Matching (α : Type*) := {a : Perm α // a*a = 1 ∧ ∀ x, a x ≠ x}

instance [Finite α] : Finite (Matching α) := inferInstanceAs
  (Finite {a : Perm α // a*a = 1 ∧ ∀ x, a x ≠ x})

instance [Fintype α] : Fintype (Matching α) := Fintype.ofFinite _

theorem matching_apply_twice (a : Matching α) (x : α) : a.val (a.val x) = x :=
  congrArg (fun p : Perm α => p x) a.property.1

theorem matching_inv (a : Matching α) : a.val⁻¹ = a.val :=
  inv_eq_of_mul_eq_one_left a.property.1

theorem matching_reverse (a b : Matching α) :
    SemiconjBy a.val (a.val*b.val) (a.val*b.val)⁻¹ := by
  change a.val*(a.val*b.val) = (a.val*b.val)⁻¹*a.val
  simp only [mul_inv_rev, matching_inv, ← mul_assoc, a.property.1, one_mul]
  rw [mul_assoc, a.property.1, mul_one]

theorem matching_reverse_zpow (a b : Matching α) (k : ℤ) (x : α) :
    a.val (((a.val*b.val)^k) x) = ((a.val*b.val)^(-k)) (a.val x) := by
  have hh := congrArg (fun p : Perm α => p x) ((matching_reverse a b).zpow_right k)
  simpa only [Perm.mul_apply, inv_zpow, zpow_neg] using hh

theorem matching_cycles_distinct (a b : Matching α) (x : α) :
    ¬ (a.val*b.val).SameCycle x (a.val x) := by
  rintro ⟨k, hk⟩
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · apply a.property.2 (((a.val*b.val)^m) x)
    rw [matching_reverse_zpow, ← hk, ← Perm.mul_apply, ← zpow_add]
    rw [hm]
    congr 2
    ring
  · apply b.property.2 (((a.val*b.val)^m) x)
    have hh := matching_reverse_zpow a b (1+m) x
    have ha : a.val*(a.val*b.val) = b.val := by rw [← mul_assoc, a.property.1, one_mul]
    rw [zpow_one_add, Perm.mul_apply, ← Perm.mul_apply, ha] at hh
    rw [hh, ← hk, ← Perm.mul_apply, ← zpow_add, hm]
    congr 2
    ring

theorem matching_cycle_reflection (a b : Matching α) (x y : α) :
    (a.val*b.val).SameCycle (a.val x) (a.val y) ↔ (a.val*b.val).SameCycle x y := by
  have hh : a.val*(a.val*b.val)*a.val⁻¹ = (a.val*b.val)⁻¹ := by
    rw [(matching_reverse a b), mul_inv_cancel_right]
  have he := Perm.sameCycle_conj (f := a.val*b.val) (g := a.val)
    (x := a.val x) (y := a.val y)
  rw [hh, Perm.sameCycle_inv] at he
  simpa only [matching_inv, matching_apply_twice] using he

def AlternatingConnected (a b : Matching α) (x y : α) : Prop :=
  (a.val*b.val).SameCycle x y ∨ (a.val*b.val).SameCycle (a.val x) y

theorem alternatingConnected_refl (a b : Matching α) (x : α) : AlternatingConnected a b x x :=
  Or.inl (Perm.SameCycle.refl _ _)

theorem alternatingConnected_symm (a b : Matching α) {x y : α}
    (h : AlternatingConnected a b x y) : AlternatingConnected a b y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · apply Or.inr
    have hh := (matching_cycle_reflection a b (a.val x) y).mpr h
    rw [matching_apply_twice] at hh
    exact hh.symm

theorem alternatingConnected_trans (a b : Matching α) {x y z : α}
    (hxy : AlternatingConnected a b x y) (hyz : AlternatingConnected a b y z) :
    AlternatingConnected a b x z := by
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact Or.inl (hxy.trans hyz)
  · exact Or.inr (((matching_cycle_reflection a b x y).mpr hxy).trans hyz)
  · exact Or.inr (hxy.trans hyz)
  · have hh := (matching_cycle_reflection a b (a.val x) y).mpr hxy
    rw [matching_apply_twice] at hh
    exact Or.inl (hh.trans hyz)

def alternatingSetoid (a b : Matching α) : Setoid α :=
  ⟨AlternatingConnected a b, alternatingConnected_refl a b,
    alternatingConnected_symm a b, alternatingConnected_trans a b⟩

theorem alternatingConnected_a (a b : Matching α) (x : α) :
    AlternatingConnected a b x (a.val x) := Or.inr (Perm.SameCycle.refl _ _)

theorem alternatingConnected_b (a b : Matching α) (x : α) :
    AlternatingConnected a b x (b.val x) := by
  apply Or.inr
  refine ⟨-1, ?_⟩
  simp only [zpow_neg_one, mul_inv_rev, matching_inv, Perm.mul_apply, matching_apply_twice]

theorem alternating_component_two_disjoint_cycles (a b : Matching α) (x : α) :
    {y | AlternatingConnected a b x y} =
      {y | (a.val*b.val).SameCycle x y} ∪ {y | (a.val*b.val).SameCycle (a.val x) y} ∧
    Disjoint {y | (a.val*b.val).SameCycle x y} {y | (a.val*b.val).SameCycle (a.val x) y} := by
  refine ⟨rfl, Set.disjoint_left.mpr ?_⟩
  intro y hxy hay
  exact matching_cycles_distinct a b x (hxy.trans hay.symm)

def matchingCycleReflectionEquiv (a b : Matching α) (x : α) :
    {y // (a.val*b.val).SameCycle x y} ≃ {y // (a.val*b.val).SameCycle (a.val x) y} where
  toFun y := ⟨a.val y.val, (matching_cycle_reflection a b x y.val).mpr y.property⟩
  invFun y := ⟨a.val y.val, by
    have hh := (matching_cycle_reflection a b (a.val x) y.val).mpr y.property
    rwa [matching_apply_twice] at hh⟩
  left_inv y := Subtype.ext (matching_apply_twice a y.val)
  right_inv y := Subtype.ext (matching_apply_twice a y.val)

theorem matching_cycle_card_equal [Fintype α] (a b : Matching α) (x : α) :
    Fintype.card {y // (a.val*b.val).SameCycle x y} =
      Fintype.card {y // (a.val*b.val).SameCycle (a.val x) y} :=
  Fintype.card_congr (matchingCycleReflectionEquiv a b x)

#print axioms matching_reverse_zpow
#print axioms matching_cycles_distinct
#print axioms matching_cycle_reflection
#print axioms alternatingConnected_trans
#print axioms alternating_component_two_disjoint_cycles
#print axioms matchingCycleReflectionEquiv
#print axioms matching_cycle_card_equal
end ConditionalSpectralExtremes.TwoMatchings
