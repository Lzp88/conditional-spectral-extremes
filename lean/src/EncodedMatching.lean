import MatchingGraphComponents
import BinaryGraphColorings

/-! An explicit actual matching on labelled pairs from a permutation and
one orientation bit per pair. The product with the fixed standard matching
acts by the permutation on one side and its inverse on the other side. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*}

def standardMatching (ι : Type*) : Matching (ι × Bool) :=
  ⟨Function.Involutive.toPerm (fun x : ι × Bool => (x.1, !x.2)) (by
    intro x
    simp only [Bool.not_not, Prod.mk.eta]), by
    constructor
    · apply Equiv.ext
      intro x
      change (x.1, !(!x.2)) = x
      simp only [Bool.not_not, Prod.mk.eta]
    · intro x hx
      have hh := congrArg Prod.snd hx
      change (!x.2) = x.2 at hh
      cases x.2 <;> simp_all⟩

@[simp] theorem standardMatching_apply (x : ι × Bool) :
    (standardMatching ι).val x = (x.1, !x.2) := rfl

def orientationOut (bits : ι → Bool) (i : ι) : ι × Bool := (i, bits i)
def orientationIn (bits : ι → Bool) (i : ι) : ι × Bool := (i, !(bits i))
def orientationColor (bits : ι → Bool) (x : ι × Bool) : Bool := Bool.xor (bits x.1) x.2

@[simp] theorem orientationColor_out (bits : ι → Bool) (i : ι) :
    orientationColor bits (orientationOut bits i) = false := by
  simp [orientationColor, orientationOut]

@[simp] theorem orientationColor_in (bits : ι → Bool) (i : ι) :
    orientationColor bits (orientationIn bits i) = true := by
  dsimp [orientationColor, orientationIn]
  cases bits i <;> rfl

theorem orientation_cases (bits : ι → Bool) (x : ι × Bool) :
    x = orientationOut bits x.1 ∨ x = orientationIn bits x.1 := by
  rcases x with ⟨i,t⟩
  cases hb : bits i <;> cases t <;> simp [orientationOut, orientationIn, hb]

def encodedPartner (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) : ι × Bool :=
  if x.2 = bits x.1 then orientationIn bits (π x.1) else orientationOut bits (π.symm x.1)

@[simp] theorem encodedPartner_out (π : Perm ι) (bits : ι → Bool) (i : ι) :
    encodedPartner π bits (orientationOut bits i) = orientationIn bits (π i) := by
  simp only [encodedPartner, orientationOut, if_true]

@[simp] theorem encodedPartner_in (π : Perm ι) (bits : ι → Bool) (i : ι) :
    encodedPartner π bits (orientationIn bits i) = orientationOut bits (π.symm i) := by
  unfold encodedPartner orientationIn
  cases bits i <;> simp

theorem encodedPartner_involutive (π : Perm ι) (bits : ι → Bool) :
    Function.Involutive (encodedPartner π bits) := by
  intro x
  rcases orientation_cases bits x with hx | hx
  · conv_lhs => rw [hx]
    rw [encodedPartner_out, encodedPartner_in, π.symm_apply_apply]
    exact hx.symm
  · conv_lhs => rw [hx]
    rw [encodedPartner_in, encodedPartner_out, π.apply_symm_apply]
    exact hx.symm

theorem encodedPartner_color (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    orientationColor bits (encodedPartner π bits x) = !(orientationColor bits x) := by
  rcases orientation_cases bits x with hx | hx
  · rw [hx, encodedPartner_out, orientationColor_in, orientationColor_out]
    rfl
  · rw [hx, encodedPartner_in, orientationColor_out, orientationColor_in]
    rfl

def encodedMatching (π : Perm ι) (bits : ι → Bool) : Matching (ι × Bool) :=
  ⟨Function.Involutive.toPerm (encodedPartner π bits) (encodedPartner_involutive π bits), by
    constructor
    · apply Equiv.ext
      intro x
      exact encodedPartner_involutive π bits x
    · intro x hx
      change encodedPartner π bits x = x at hx
      have hh := encodedPartner_color π bits x
      rw [hx] at hh
      cases orientationColor bits x <;> simp_all⟩

@[simp] theorem encodedMatching_apply (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    (encodedMatching π bits).val x = encodedPartner π bits x := rfl

theorem standardMatching_color (bits : ι → Bool) (x : ι × Bool) :
    orientationColor bits ((standardMatching ι).val x) = !(orientationColor bits x) := by
  rcases x with ⟨i,t⟩
  dsimp [orientationColor, standardMatching]
  cases bits i <;> cases t <;> rfl

def encodedColoring (π : Perm ι) (bits : ι → Bool) :
    BinaryColoring (matchingGraph (standardMatching ι) (encodedMatching π bits)) :=
  ⟨orientationColor bits, by
    intro x y h
    rcases h with h | h
    · subst y
      rw [standardMatching_color, Bool.not_not]
    · subst y
      rw [encodedMatching_apply, encodedPartner_color, Bool.not_not]⟩

theorem encoded_product_out (π : Perm ι) (bits : ι → Bool) (i : ι) :
    ((standardMatching ι).val*(encodedMatching π bits).val) (orientationOut bits i) =
      orientationOut bits (π i) := by
  rw [Perm.mul_apply, encodedMatching_apply, encodedPartner_out, standardMatching_apply]
  simp only [orientationIn, orientationOut, Bool.not_not]

theorem encoded_product_in (π : Perm ι) (bits : ι → Bool) (i : ι) :
    ((standardMatching ι).val*(encodedMatching π bits).val) (orientationIn bits i) =
      orientationIn bits (π.symm i) := by
  rw [Perm.mul_apply, encodedMatching_apply, encodedPartner_in, standardMatching_apply]
  rfl

#print axioms standardMatching
#print axioms encodedPartner_involutive
#print axioms encodedMatching
#print axioms encodedColoring
#print axioms encoded_product_out
#print axioms encoded_product_in
end ConditionalSpectralExtremes.TwoMatchings
