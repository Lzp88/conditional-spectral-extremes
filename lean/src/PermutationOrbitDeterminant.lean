import PermutationOrbitLabels
import CyclicPermutationDeterminant
import Mathlib.LinearAlgebra.Matrix.Block

/-! Determinant factorization for an actual finite permutation matrix, over
any commutative ring. The factors are its genuine SameCycle orbit fibers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes
open Equiv Matrix
variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

omit [Fintype α] [DecidableEq α] in
theorem permutationOrbitClass_apply (σ : Perm α) (x : α) :
    permutationOrbitClass σ (σ x)=permutationOrbitClass σ x :=
  (permutationOrbitClass_eq_iff σ _ _).mpr ((Perm.SameCycle.refl σ x).apply_left)

def permutationOrbitPerm (σ : Perm α) (q : PermutationOrbit σ) : Perm (PermutationOrbitFiber σ q) :=
  σ.subtypePerm (fun x => by rw [permutationOrbitClass_apply])

omit [Fintype α] [DecidableEq α] in
theorem permutationOrbitPerm_transitive (σ : Perm α) (q : PermutationOrbit σ)
    (x y : PermutationOrbitFiber σ q) : (permutationOrbitPerm σ q).SameCycle x y := by
  apply Perm.sameCycle_subtypePerm.mpr
  exact (permutationOrbitClass_eq_iff σ x.val y.val).mp (x.property.trans y.property.symm)

omit [Fintype α] [DecidableEq α] in
theorem permutationOrbitFiber_nonempty (σ : Perm α) (q : PermutationOrbit σ) :
    Nonempty (PermutationOrbitFiber σ q) := by
  induction q using Quotient.inductionOn with | h x => exact ⟨⟨x,rfl⟩⟩

omit [Fintype α] in
theorem permutation_orbit_block (σ : Perm α) (q : PermutationOrbit σ) (z : R) :
    (1-z • σ.permMatrix R).toSquareBlock (permutationOrbitClass σ) q =
      1-z • (permutationOrbitPerm σ q).permMatrix R := by
  ext i j
  simp only [Matrix.toSquareBlock_def,Matrix.of_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.one_apply,permMatrix_entry,permutationOrbitPerm,
    Perm.subtypePerm_apply,Subtype.ext_iff]

theorem permutation_orbit_block_determinant (σ : Perm α) (q : PermutationOrbit σ) (z : R) :
    ((1-z • σ.permMatrix R).toSquareBlock (permutationOrbitClass σ) q).det =
      1-z^(Nat.card (PermutationOrbitFiber σ q)) := by
  rw [permutation_orbit_block,Nat.card_eq_fintype_card]
  by_cases hσ : permutationOrbitPerm σ q=1
  · let _ : Nonempty (PermutationOrbitFiber σ q) := permutationOrbitFiber_nonempty σ q
    let _ : Subsingleton (PermutationOrbitFiber σ q) := ⟨fun x y => by
      have hh := permutationOrbitPerm_transitive σ q x y
      rw [hσ,Perm.sameCycle_one] at hh
      exact hh⟩
    let x : PermutationOrbitFiber σ q := Classical.choice (permutationOrbitFiber_nonempty σ q)
    let _ : Unique (PermutationOrbitFiber σ q) := uniqueOfSubsingleton x
    rw [Fintype.card_unique,pow_one,Matrix.det_eq_elem_of_subsingleton _ x]
    simp only [hσ,Matrix.sub_apply,Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,
      permMatrix_entry,Perm.one_apply,if_true,mul_one]
  · exact cyclic_permutation_determinant (permutationOrbitPerm σ q)
      (permutationOrbitPerm_transitive σ q) hσ z

theorem permutation_orbit_determinant (σ : Perm α) (z : R) :
    (1-z • σ.permMatrix R).det =
      ∏ q : PermutationOrbit σ, (1-z^(Nat.card (PermutationOrbitFiber σ q))) := by
  let _ : LinearOrder (PermutationOrbit σ) := LinearOrder.lift'
    (Fintype.equivFin (PermutationOrbit σ)) (Fintype.equivFin _).injective
  have hblock : Matrix.BlockTriangular (1-z • σ.permMatrix R) (permutationOrbitClass σ) := by
    intro i j hij
    have hij' : i≠j := by
      intro he
      subst j
      exact (lt_irrefl _ hij)
    have hσij : σ i≠j := by
      intro he
      have heq : permutationOrbitClass σ j=permutationOrbitClass σ i :=
        he ▸ permutationOrbitClass_apply σ i
      exact (ne_of_lt hij) heq
    simp only [Matrix.sub_apply,Matrix.one_apply,if_neg hij',Matrix.smul_apply,smul_eq_mul,
      permMatrix_entry,if_neg hσij,mul_zero,sub_self]
  rw [hblock.det_fintype]
  exact Finset.prod_congr rfl (fun q _ => permutation_orbit_block_determinant σ q z)

#print axioms permutation_orbit_determinant
end ConditionalSpectralExtremes
