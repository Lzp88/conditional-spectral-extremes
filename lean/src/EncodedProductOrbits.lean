import MatchingComponentProfile

/-! Product cycles are labeled by one permutation orbit and one of the
two color classes. This includes singleton product cycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*}

abbrev encodedProduct (π : Perm ι) (bits : ι → Bool) : Perm (ι × Bool) :=
  (standardMatching ι).val * (encodedMatching π bits).val

theorem encoded_product_color (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    orientationColor bits (encodedProduct π bits x)=orientationColor bits x := by
  change orientationColor bits ((standardMatching ι).val ((encodedMatching π bits).val x))=_
  rw [standardMatching_color, encodedMatching_apply, encodedPartner_color, Bool.not_not]

theorem encoded_product_pow_color (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) (k : Nat) :
    orientationColor bits (((encodedProduct π bits)^k) x)=orientationColor bits x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, encoded_product_color, ih]

theorem encoded_product_pow_in (π : Perm ι) (bits : ι → Bool) (i : ι) (k : Nat) :
    (((encodedProduct π bits)^k) (orientationIn bits i))=
      orientationIn bits (((π⁻¹)^k) i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, encoded_product_in, pow_succ', Perm.mul_apply]
    rfl

theorem encoded_product_sameCycle_iff [Finite ι] (π : Perm ι) (bits : ι → Bool) (x y : ι × Bool) :
    (encodedProduct π bits).SameCycle x y ↔
      π.SameCycle x.1 y.1 ∧ orientationColor bits x=orientationColor bits y := by
  constructor
  · intro h
    refine ⟨encoded_reachable_sameCycle π bits
      (matchingGraph_reachable_of_sameCycle (standardMatching ι) (encodedMatching π bits) h), ?_⟩
    obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    exact (encoded_product_pow_color π bits x k).symm
  · rintro ⟨h,hc⟩
    rcases orientation_cases bits x with hx | hx <;>
      rcases orientation_cases bits y with hy | hy
    · obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
      refine ⟨(k:ℤ),?_⟩
      rw [zpow_natCast, hx, encoded_product_pow_out, hk]
      exact hy.symm
    · rw [hx,hy,orientationColor_out,orientationColor_in] at hc
      cases hc
    · rw [hx,hy,orientationColor_in,orientationColor_out] at hc
      cases hc
    · obtain ⟨k,hk⟩ := h.inv.exists_nat_pow_eq
      refine ⟨(k:ℤ),?_⟩
      rw [zpow_natCast, hx, encoded_product_pow_in, hk]
      exact hy.symm

def encodedProductOrbitLabel [Finite ι] (π : Perm ι) (bits : ι → Bool) :
    PermutationOrbit (encodedProduct π bits) → PermutationOrbit π × Bool :=
  Quotient.lift (fun x => (permutationOrbitClass π x.1, orientationColor bits x)) (by
    intro x y h
    have hh := (encoded_product_sameCycle_iff π bits x y).mp h
    exact Prod.ext (Quotient.sound hh.1) hh.2)

theorem encodedProductOrbitLabel_bijective [Finite ι] (π : Perm ι) (bits : ι → Bool) :
    Function.Bijective (encodedProductOrbitLabel π bits) := by
  constructor
  · intro q r
    induction q using Quotient.inductionOn with | h x =>
      induction r using Quotient.inductionOn with | h y =>
        intro h
        apply Quotient.sound
        apply (encoded_product_sameCycle_iff π bits x y).mpr
        exact ⟨Quotient.exact (congrArg Prod.fst h), congrArg Prod.snd h⟩
  · rintro ⟨q,t⟩
    induction q using Quotient.inductionOn with | h i =>
      cases t with
      | false =>
        refine ⟨permutationOrbitClass _ (orientationOut bits i),?_⟩
        exact Prod.ext rfl (orientationColor_out bits i)
      | true =>
        refine ⟨permutationOrbitClass _ (orientationIn bits i),?_⟩
        exact Prod.ext rfl (orientationColor_in bits i)

def encodedProductOrbitEquiv [Finite ι] (π : Perm ι) (bits : ι → Bool) :
    PermutationOrbit (encodedProduct π bits) ≃ PermutationOrbit π × Bool :=
  Equiv.ofBijective (encodedProductOrbitLabel π bits) (encodedProductOrbitLabel_bijective π bits)

theorem encodedProductOrbitEquiv_class [Finite ι] (π : Perm ι) (bits : ι → Bool) (x : ι × Bool) :
    encodedProductOrbitEquiv π bits (permutationOrbitClass _ x)=
      (permutationOrbitClass π x.1, orientationColor bits x) := rfl

def orientedVertex (bits : ι → Bool) (i : ι) (t : Bool) : ι × Bool :=
  if t then orientationIn bits i else orientationOut bits i

theorem orientedVertex_fst (bits : ι → Bool) (i : ι) (t : Bool) :
    (orientedVertex bits i t).1=i := by cases t <;> rfl

theorem orientedVertex_color (bits : ι → Bool) (i : ι) (t : Bool) :
    orientationColor bits (orientedVertex bits i t)=t := by
  cases t <;> simp only [orientedVertex, Bool.false_eq_true, ite_false, ite_true,
    orientationColor_out, orientationColor_in]

theorem orientedVertex_recover (bits : ι → Bool) (x : ι × Bool) :
    orientedVertex bits x.1 (orientationColor bits x)=x := by
  rcases orientation_cases bits x with hx | hx
  · rw [hx, orientationColor_out]
    rfl
  · rw [hx, orientationColor_in]
    rfl

def encodedProductOrbitFiberEquiv [Finite ι] (π : Perm ι) (bits : ι → Bool)
    (q : PermutationOrbit (encodedProduct π bits)) :
    PermutationOrbitFiber (encodedProduct π bits) q ≃
      PermutationOrbitFiber π (encodedProductOrbitEquiv π bits q).1 where
  toFun x := ⟨x.val.1, by
    exact congrArg (fun r => (encodedProductOrbitEquiv π bits r).1) x.property⟩
  invFun i := ⟨orientedVertex bits i.val (encodedProductOrbitEquiv π bits q).2, by
    apply (encodedProductOrbitEquiv π bits).injective
    rw [encodedProductOrbitEquiv_class]
    apply Prod.ext
    · rw [orientedVertex_fst]
      exact i.property
    · exact orientedVertex_color _ _ _⟩
  left_inv x := by
    apply Subtype.ext
    change orientedVertex bits x.val.1 (encodedProductOrbitEquiv π bits q).2=x.val
    have hh := congrArg (fun r => (encodedProductOrbitEquiv π bits r).2) x.property
    change orientationColor bits x.val=(encodedProductOrbitEquiv π bits q).2 at hh
    rw [← hh]
    exact orientedVertex_recover bits x.val
  right_inv i := by apply Subtype.ext; exact orientedVertex_fst _ _ _

theorem encodedProductOrbitFiber_card [Finite ι] (π : Perm ι) (bits : ι → Bool)
    (q : PermutationOrbit (encodedProduct π bits)) :
    Nat.card (PermutationOrbitFiber (encodedProduct π bits) q)=
      Nat.card (PermutationOrbitFiber π (encodedProductOrbitEquiv π bits q).1) :=
  Nat.card_congr (encodedProductOrbitFiberEquiv π bits q)

#print axioms encoded_product_sameCycle_iff
#print axioms encodedProductOrbitEquiv
#print axioms encodedProductOrbitFiber_card
end ConditionalSpectralExtremes.TwoMatchings
