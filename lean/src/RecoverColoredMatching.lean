import EncodedMatching

/-! Explicit inverse to the permutation-and-bits encoding. Its domain is
the actual fixed-point-free matching with a valid coloring of its union
with the fixed standard matching. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*}

abbrev StandardColoring (b : Matching (ι × Bool)) :=
  BinaryColoring (matchingGraph (standardMatching ι) b)

def coloringBits {b : Matching (ι × Bool)} (c : StandardColoring b) : ι → Bool :=
  fun i => c.val (i, false)

theorem coloring_eq_orientation {b : Matching (ι × Bool)} (c : StandardColoring b) (x : ι × Bool) :
    c.val x = orientationColor (coloringBits c) x := by
  rcases x with ⟨i,t⟩
  cases t with
  | false => simp [coloringBits, orientationColor]
  | true =>
    have hh : c.val (i,true) = !(c.val (i,false)) :=
      c.property (matchingGraph_adj_a (standardMatching ι) b (i,true))
    rw [hh]
    dsimp [coloringBits, orientationColor]
    cases c.val (i,false) <;> rfl

theorem coloring_out {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) :
    c.val (orientationOut (coloringBits c) i) = false := by
  rw [coloring_eq_orientation, orientationColor_out]

theorem coloring_in {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) :
    c.val (orientationIn (coloringBits c) i) = true := by
  rw [coloring_eq_orientation, orientationColor_in]

theorem coloring_false_iff {b : Matching (ι × Bool)} (c : StandardColoring b) (x : ι × Bool) :
    c.val x = false ↔ x.2 = coloringBits c x.1 := by
  rw [coloring_eq_orientation]
  unfold orientationColor
  cases coloringBits c x.1 <;> cases x.2 <;> decide

theorem coloring_true_iff {b : Matching (ι × Bool)} (c : StandardColoring b) (x : ι × Bool) :
    c.val x = true ↔ x.2 = !(coloringBits c x.1) := by
  rw [coloring_eq_orientation]
  unfold orientationColor
  cases coloringBits c x.1 <;> cases x.2 <;> decide

theorem colored_partner_flips {b : Matching (ι × Bool)} (c : StandardColoring b) (x : ι × Bool) :
    c.val (b.val x) = !(c.val x) :=
  c.property (matchingGraph_adj_b (standardMatching ι) b x).symm

def coloredForward {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) : ι :=
  (b.val (orientationOut (coloringBits c) i)).1

def coloredBackward {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) : ι :=
  (b.val (orientationIn (coloringBits c) i)).1

theorem colored_partner_out {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) :
    b.val (orientationOut (coloringBits c) i) = orientationIn (coloringBits c) (coloredForward c i) := by
  apply Prod.ext
  · rfl
  apply (coloring_true_iff c _).mp
  rw [colored_partner_flips, coloring_out]
  rfl

theorem colored_partner_in {b : Matching (ι × Bool)} (c : StandardColoring b) (i : ι) :
    b.val (orientationIn (coloringBits c) i) = orientationOut (coloringBits c) (coloredBackward c i) := by
  apply Prod.ext
  · rfl
  apply (coloring_false_iff c _).mp
  rw [colored_partner_flips, coloring_in]
  rfl

def recoverPermutation {b : Matching (ι × Bool)} (c : StandardColoring b) : Perm ι where
  toFun := coloredForward c
  invFun := coloredBackward c
  left_inv i := by
    have hh := matching_apply_twice b (orientationOut (coloringBits c) i)
    rw [colored_partner_out c, colored_partner_in c] at hh
    exact congrArg Prod.fst hh
  right_inv i := by
    have hh := matching_apply_twice b (orientationIn (coloringBits c) i)
    rw [colored_partner_in c, colored_partner_out c] at hh
    exact congrArg Prod.fst hh

theorem recover_encoded_matching {b : Matching (ι × Bool)} (c : StandardColoring b) :
    encodedMatching (recoverPermutation c) (coloringBits c) = b := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rcases orientation_cases (coloringBits c) x with hx | hx
  · rw [hx, encodedMatching_apply, encodedPartner_out, colored_partner_out c]
    rfl
  · rw [hx, encodedMatching_apply, encodedPartner_in, colored_partner_in c]
    rfl

theorem coloringBits_encoded (π : Perm ι) (bits : ι → Bool) :
    coloringBits (encodedColoring π bits) = bits := by
  funext i
  simp [coloringBits, encodedColoring, orientationColor]

theorem recoverPermutation_encoded (π : Perm ι) (bits : ι → Bool) :
    recoverPermutation (encodedColoring π bits) = π := by
  apply Equiv.ext
  intro i
  change ((encodedMatching π bits).val
    (orientationOut (coloringBits (encodedColoring π bits)) i)).1 = π i
  rw [coloringBits_encoded, encodedMatching_apply, encodedPartner_out]
  rfl

abbrev ColoredMatching (ι : Type*) := Σ b : Matching (ι × Bool), StandardColoring b

def coloredMatchingEquiv (ι : Type*) : ColoredMatching ι ≃ (Perm ι × (ι → Bool)) where
  toFun bc := (recoverPermutation bc.2, coloringBits bc.2)
  invFun pb := ⟨encodedMatching pb.1 pb.2, encodedColoring pb.1 pb.2⟩
  left_inv bc := by
    rcases bc with ⟨b,c⟩
    apply Sigma.ext (recover_encoded_matching c)
    apply (Subtype.heq_iff_coe_eq (by intro f; dsimp only; rw [recover_encoded_matching c])).mpr
    funext x
    exact (coloring_eq_orientation c x).symm
  right_inv pb := by
    rcases pb with ⟨π,bits⟩
    exact Prod.ext (recoverPermutation_encoded π bits) (coloringBits_encoded π bits)

#print axioms recoverPermutation
#print axioms recover_encoded_matching
#print axioms recoverPermutation_encoded
#print axioms coloredMatchingEquiv
end ConditionalSpectralExtremes.TwoMatchings
