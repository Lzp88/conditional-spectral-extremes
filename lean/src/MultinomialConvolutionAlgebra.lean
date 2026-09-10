import FiniteMultinomial

/-! Exact convolution of the actual finite multinomial masses. Polynomial
extensionality is applied to the already proved real generating function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def countMonomialExponent {k : ℕ} (c : countFiber ι k k) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (c.val i).val)

@[simp] theorem countMonomialExponent_apply {k : ℕ} (c : countFiber ι k k) (i : ι) :
    countMonomialExponent c i = (c.val i).val := rfl

theorem countMonomialExponent_injective (k : ℕ) :
    Function.Injective (countMonomialExponent : countFiber ι k k → ι →₀ ℕ) := by
  intro c d h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun x : ι →₀ ℕ => x i) h

def multinomialPolynomial (p : ι → ℝ) (k : ℕ) : MvPolynomial ι ℝ :=
  ∑ c : countFiber ι k k, MvPolynomial.monomial (countMonomialExponent c) (multinomialMass p k c)

theorem multinomialPolynomial_eval (p z : ι → ℝ) (k : ℕ) :
    MvPolynomial.eval z (multinomialPolynomial p k) = (∑ i, p i*z i)^k := by
  unfold multinomialPolynomial
  rw [map_sum]
  simp_rw [MvPolynomial.eval_monomial]
  have hh (c : countFiber ι k k) : (countMonomialExponent c).prod (fun i e => z i^e) =
      ∏ i, z i^(c.val i).val := by
    simpa only [countMonomialExponent_apply] using
      (countMonomialExponent c).prod_fintype (fun i e => z i^e) (fun _ => pow_zero _)
  simp_rw [hh]
  exact multinomial_generating_function p z k

theorem multinomialPolynomial_eq (p : ι → ℝ) (k : ℕ) :
    multinomialPolynomial p k = (∑ i, MvPolynomial.C (p i)*MvPolynomial.X i)^k := by
  apply MvPolynomial.funext
  intro z
  rw [multinomialPolynomial_eval]
  simp

theorem multinomialPolynomial_mul (p : ι → ℝ) (m n : ℕ) :
    multinomialPolynomial p m*multinomialPolynomial p n = multinomialPolynomial p (m+n) := by
  rw [multinomialPolynomial_eq, multinomialPolynomial_eq, multinomialPolynomial_eq, pow_add]

theorem multinomialPolynomial_coeff (p : ι → ℝ) (k : ℕ) (c : countFiber ι k k) :
    MvPolynomial.coeff (countMonomialExponent c) (multinomialPolynomial p k) = multinomialMass p k c := by
  classical
  unfold multinomialPolynomial
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, (countMonomialExponent_injective k).eq_iff]
  simp

theorem multinomial_mass_convolution (p : ι → ℝ) (m n : ℕ) (c : countFiber ι (m+n) (m+n)) :
    (∑ u : countFiber ι m m, ∑ v : countFiber ι n n,
      if ∀ i, (u.val i).val+(v.val i).val = (c.val i).val then
        multinomialMass p m u*multinomialMass p n v else 0) = multinomialMass p (m+n) c := by
  classical
  have hh := congrArg (MvPolynomial.coeff (countMonomialExponent c)) (multinomialPolynomial_mul p m n)
  rw [multinomialPolynomial_coeff] at hh
  simp only [multinomialPolynomial, Finset.sum_mul, Finset.mul_sum,
    MvPolynomial.coeff_sum, MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial] at hh
  have he (u : countFiber ι m m) (v : countFiber ι n n) :
      countMonomialExponent u+countMonomialExponent v = countMonomialExponent c ↔
        ∀ i, (u.val i).val+(v.val i).val = (c.val i).val := by
    rw [Finsupp.ext_iff]
    rfl
  rw [Finset.sum_comm]
  simpa only [he] using hh

def addCountState {m n : ℕ} (u : countFiber ι m m) (v : countFiber ι n n) :
    countFiber ι (m+n) (m+n) :=
  ⟨fun i => ⟨(u.val i).val+(v.val i).val, by have hu := (u.val i).isLt; have hv := (v.val i).isLt; omega⟩,
    by simp only [Finset.sum_add_distrib, u.property, v.property]⟩

theorem addCountState_eq_iff {m n : ℕ} (u : countFiber ι m m) (v : countFiber ι n n)
    (c : countFiber ι (m+n) (m+n)) : addCountState u v = c ↔
      ∀ i, (u.val i).val+(v.val i).val = (c.val i).val := by
  constructor
  · intro h i
    exact congrArg (fun w : countFiber ι (m+n) (m+n) => (w.val i).val) h
  · intro h
    apply Subtype.ext
    funext i
    exact Fin.ext (h i)

#print axioms countMonomialExponent_injective
#print axioms multinomialPolynomial_eval
#print axioms multinomialPolynomial_eq
#print axioms multinomialPolynomial_mul
#print axioms multinomialPolynomial_coeff
#print axioms multinomial_mass_convolution
#print axioms addCountState
#print axioms addCountState_eq_iff

end ConditionalSpectralExtremes.BlockCounts
