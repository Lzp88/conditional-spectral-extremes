import CyclicPermutationSelection
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Direct determinant calculation for a genuine transitive nontrivial
permutation. The proof enumerates the actual Leibniz terms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes
open Equiv Matrix

theorem det_apply_rows {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (M : Matrix α α R) :
    M.det=∑ ρ : Perm α, ((Perm.sign ρ : Int) : R)*∏ i, M i (ρ i) := by
  rw [← Matrix.det_transpose,Matrix.det_apply']
  rfl

theorem permMatrix_entry {α R : Type*} [DecidableEq α] [Zero R] [One R]
    (σ : Perm α) (i j : α) : σ.permMatrix R i j=if σ i=j then 1 else 0 := by
  simp only [Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_def,Option.some.injEq]

theorem cyclic_permutation_determinant {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (σ : Perm α) (hcycle : ∀ x y, σ.SameCycle x y) (hne : σ≠1) (z : R) :
    (1-z • σ.permMatrix R).det=1-z^(Fintype.card α) := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, σ x≠x := by
    by_contra hh
    apply hne
    ext x
    exact not_not.mp ((not_exists.mp hh) x)
  have hfree (i : α) : σ i≠i := by
    intro h
    exact hx ((hcycle x i).apply_eq_self_iff.mpr h)
  have hiscycle : σ.IsCycle := ⟨x,hx,fun y _ => hcycle x y⟩
  have hsupport : σ.support=Finset.univ := by
    ext i
    simp only [Perm.mem_support,Finset.mem_univ,iff_true]
    exact hfree i
  let M : Matrix α α R := 1-z • σ.permMatrix R
  let f : Perm α → R := fun ρ => ((Perm.sign ρ : Int) : R)*∏ i, M i (ρ i)
  have hzero (ρ : Perm α) (hρ : ρ ∉ ({1,σ} : Finset (Perm α))) : f ρ=0 := by
    obtain ⟨i,hi,hsi⟩ : ∃ i, ρ i≠i ∧ ρ i≠σ i := by
      by_contra hh
      have hh' : ∀ i, ρ i=i ∨ ρ i=σ i := by
        intro i
        simpa only [not_exists,not_and_or,not_not] using (not_exists.mp hh) i
      have ht := permutation_cycle_selection σ ρ hcycle hh'
      exact hρ (by simpa only [Finset.mem_insert,Finset.mem_singleton] using ht)
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [M,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
      permMatrix_entry,if_neg hi.symm,if_neg hsi.symm,mul_zero,sub_self]
  have hsum : (∑ ρ ∈ ({1,σ} : Finset (Perm α)), f ρ)=∑ ρ, f ρ :=
    Finset.sum_subset (Finset.subset_univ _) (fun ρ _ hρ => hzero ρ hρ)
  have hdiag : f 1=1 := by
    have hentry (i : α) : M i i=1 := by
      simp only [M,Matrix.sub_apply,Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,
        permMatrix_entry,if_neg (hfree i),mul_zero,sub_zero]
    simp only [f,Perm.one_apply,Perm.sign_one,Units.val_one,Int.cast_one,
      hentry,Finset.prod_const_one,mul_one]
  have hcyc : f σ= -z^(Fintype.card α) := by
    have hentry (i : α) : M i (σ i)= -z := by
      simp only [M,Matrix.sub_apply,Matrix.one_apply,if_neg (hfree i).symm,
        Matrix.smul_apply,smul_eq_mul,permMatrix_entry,if_true,mul_one,zero_sub]
    have hprod : (∏ i, M i (σ i))=(-z)^(Fintype.card α) := by
      simp only [hentry,Finset.prod_const,Finset.card_univ]
    have hsignR : ((Perm.sign σ : Int) : R)= -(-1 : R)^(Fintype.card α) := by
      rw [hiscycle.sign,hsupport]
      simp only [Finset.card_univ,Units.val_neg,Units.val_pow_eq_pow_val,Units.val_one,
        Int.cast_neg,Int.cast_pow,Int.cast_one]
    change ((Perm.sign σ : Int) : R)*(∏ i, M i (σ i))= -z^(Fintype.card α)
    rw [hprod,hsignR,neg_pow]
    calc
      _ = -(((-1 : R)*(-1))^(Fintype.card α)*z^(Fintype.card α)) := by rw [mul_pow]; ring
      _ = _ := by simp
  rw [det_apply_rows]
  change (∑ ρ, f ρ)=_
  rw [← hsum,Finset.sum_pair (Ne.symm hne),hdiag,hcyc]
  exact (sub_eq_add_neg _ _).symm

#print axioms cyclic_permutation_determinant
end ConditionalSpectralExtremes
