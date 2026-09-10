import MatchingOrbitAlgebra
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Every fixed-point-free involution on the same finite labeled space
is a genuine conjugate. Conjugation preserves both defining properties. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {α : Type*}

def conjugateMatching (g : Perm α) (a : Matching α) : Matching α :=
  ⟨g*a.val*g⁻¹, by
    constructor
    · calc
        (g*a.val*g⁻¹)*(g*a.val*g⁻¹)=g*(a.val*a.val)*g⁻¹ := by group
        _=1 := by rw [a.property.1]; group
    · intro x hx
      apply a.property.2 (g⁻¹ x)
      have hh := congrArg (fun y => g⁻¹ y) hx
      simpa using hh⟩

theorem conjugateMatching_val (g : Perm α) (a : Matching α) :
    (conjugateMatching g a).val=g*a.val*g⁻¹ := rfl

theorem conjugateMatching_one (a : Matching α) : conjugateMatching 1 a=a := by
  apply Subtype.ext
  simp [conjugateMatching]

theorem conjugateMatching_mul (g h : Perm α) (a : Matching α) :
    conjugateMatching (g*h) a=conjugateMatching g (conjugateMatching h a) := by
  apply Subtype.ext
  simp only [conjugateMatching_val, mul_inv_rev]
  group

def conjugateMatchingEquiv (g : Perm α) : Matching α ≃ Matching α where
  toFun := conjugateMatching g
  invFun := conjugateMatching g⁻¹
  left_inv a := by rw [← conjugateMatching_mul, inv_mul_cancel, conjugateMatching_one]
  right_inv a := by rw [← conjugateMatching_mul, mul_inv_cancel, conjugateMatching_one]

theorem matching_support [Fintype α] [DecidableEq α] (a : Matching α) :
    a.val.support=Finset.univ := by
  ext x
  simp only [Perm.mem_support, Finset.mem_univ, iff_true]
  exact a.property.2 x

theorem matching_cycleType [Fintype α] [DecidableEq α] (a : Matching α) :
    a.val.cycleType=Multiset.replicate (Fintype.card α / 2) 2 := by
  have hh := Perm.cycleType_of_pow_prime_eq_one (p:=2)
    (show a.val^2=1 by rw [pow_two]; exact a.property.1)
  have hc := a.val.sum_cycleType
  rw [hh, Multiset.sum_replicate, nsmul_eq_mul, matching_support, Finset.card_univ] at hc
  rw [hh]
  congr 1
  exact Nat.eq_div_of_mul_eq_right (by omega : 2 ≠ 0) (by simpa only [Nat.cast_id, mul_comm] using hc)

theorem matchings_isConj [Fintype α] [DecidableEq α] (a b : Matching α) :
    IsConj a.val b.val :=
  Perm.isConj_of_cycleType_eq ((matching_cycleType a).trans (matching_cycleType b).symm)

theorem conjugateMatching_surjective [Fintype α] (a : Matching α) :
    Function.Surjective (fun g : Perm α => conjugateMatching g a) := by
  let := Classical.decEq α
  intro b
  obtain ⟨g,hg⟩ := isConj_iff.mp (matchings_isConj a b)
  exact ⟨g, Subtype.ext hg⟩

def conjugateFiberEquiv (a b : Matching α) (g : Perm α) :
    {h : Perm α // conjugateMatching h a=b} ≃
      {h : Perm α // conjugateMatching h a=conjugateMatching g b} where
  toFun h := ⟨g*h.val, by rw [conjugateMatching_mul, h.property]⟩
  invFun h := ⟨g⁻¹*h.val, by
    rw [conjugateMatching_mul, h.property, ← conjugateMatching_mul,
      inv_mul_cancel, conjugateMatching_one]⟩
  left_inv h := by apply Subtype.ext; group
  right_inv h := by apply Subtype.ext; group

theorem conjugateMatching_fibers_card [Fintype α] (a b c : Matching α) :
    Nat.card {g : Perm α // conjugateMatching g a=b}=
      Nat.card {g : Perm α // conjugateMatching g a=c} := by
  obtain ⟨g,rfl⟩ := conjugateMatching_surjective b c
  exact Nat.card_congr (conjugateFiberEquiv a b g)

theorem conjugateMatching_fiber_card_pos [Fintype α] (a b : Matching α) :
    0 < Nat.card {g : Perm α // conjugateMatching g a=b} := by
  obtain ⟨g,hg⟩ := conjugateMatching_surjective a b
  let : Nonempty {g : Perm α // conjugateMatching g a=b} := ⟨⟨g,hg⟩⟩
  exact Nat.card_pos

#print axioms matching_cycleType
#print axioms conjugateMatching_surjective
#print axioms conjugateMatching_fibers_card
end ConditionalSpectralExtremes.TwoMatchings
