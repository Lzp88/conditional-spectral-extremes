import PermutationOrbitProducts
import PermutationOrbitDeterminant
import PermutationProfileCardinality

/-! The exact characteristic-polynomial identity for the genuine matrix
of a permutation, and equality with the conventional charpoly maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes
open Equiv Matrix

def permutationDetPolynomial {n : Nat} (σ : Perm (Fin n)) : Polynomial Complex :=
  (1-(Polynomial.X : Polynomial Complex) • σ.permMatrix (Polynomial Complex)).det

theorem actual_permutation_determinant_polynomial {n : Nat} (σ : Perm (Fin n)) :
    permutationDetPolynomial σ=characteristicPolynomial (permutationConfiguration σ) := by
  unfold permutationDetPolynomial
  rw [permutation_orbit_determinant,permutation_orbit_cycle_product σ
    (fun j => 1-(Polynomial.X : Polynomial Complex)^j)]
  rfl

theorem actual_permutation_determinant {n : Nat} (σ : Perm (Fin n)) (z : Complex) :
    (1-z • σ.permMatrix Complex).det=
      (characteristicPolynomial (permutationConfiguration σ)).eval z := by
  rw [permutation_orbit_determinant,permutation_orbit_cycle_product σ (fun j => 1-z^j)]
  simp only [characteristicPolynomial,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X]

def permutationMaximumLogModulus {n : Nat} (σ : Perm (Fin n)) : Real :=
  Real.log (circleNorm (permutationDetPolynomial σ))

theorem permutationMaximumLogModulus_eq_profile {n : Nat} (σ : Perm (Fin n)) :
    permutationMaximumLogModulus σ=maximumLogModulus (permutationConfiguration σ) := by
  rw [permutationMaximumLogModulus,actual_permutation_determinant_polynomial]
  rfl

theorem permutationConfiguration_inv {n : Nat} (σ : Perm (Fin n)) :
    permutationConfiguration σ⁻¹=permutationConfiguration σ := by
  apply (permutationConfiguration_eq_iff_partition _ _).mpr
  apply Nat.Partition.ext
  simp only [Perm.parts_partition,Perm.cycleType_inv,Perm.support_inv]

theorem norm_permutation_det_neg {n : Nat} (σ : Perm (Fin n)) :
    ‖(-(σ.permMatrix Complex)).det‖=1 := by
  rw [Matrix.det_neg,Matrix.det_permutation,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

theorem actual_permutation_charpoly_norm {n : Nat} (σ : Perm (Fin n)) (z : Complex) :
    ‖(z • (1 : Matrix (Fin n) (Fin n) Complex)-σ.permMatrix Complex).det‖=
      ‖(characteristicPolynomial (permutationConfiguration σ)).eval z‖ := by
  have hmul : σ.permMatrix Complex*(σ⁻¹).permMatrix Complex=1 := by
    rw [← Matrix.permMatrix_mul]
    simp only [inv_mul_cancel,Matrix.permMatrix_one]
  have hf : -(σ.permMatrix Complex)*(1-z • (σ⁻¹).permMatrix Complex)=
      z • (1 : Matrix (Fin n) (Fin n) Complex)-σ.permMatrix Complex := by
    simp only [Matrix.neg_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,hmul,
      smul_neg,sub_neg_eq_add,add_comm]
    exact (sub_eq_add_neg _ _).symm
  rw [← hf,Matrix.det_mul,norm_mul,norm_permutation_det_neg,one_mul,
    actual_permutation_determinant,permutationConfiguration_inv]

theorem actual_permutation_charpoly_circleNorm {n : Nat} (σ : Perm (Fin n)) :
    circleNorm (σ.permMatrix Complex).charpoly=
      circleNorm (characteristicPolynomial (permutationConfiguration σ)) := by
  unfold circleNorm
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq,Matrix.eval_charpoly,Matrix.scalar_apply,← Matrix.smul_one_eq_diagonal,
    actual_permutation_charpoly_norm]

#print axioms actual_permutation_determinant
#print axioms permutationMaximumLogModulus_eq_profile
#print axioms actual_permutation_charpoly_circleNorm
end ConditionalSpectralExtremes
