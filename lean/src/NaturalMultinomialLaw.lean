import FiniteMultinomial

/-! The same actual multinomial law on natural-valued count vectors, with
the sample size allowed to vary. This is the common space for Poisson mixing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def naturalCountVector {k : ℕ} (c : countFiber ι k k) : ι → ℕ := fun i => (c.val i).val

theorem naturalCountVector_sum {k : ℕ} (c : countFiber ι k k) :
    (∑ i, naturalCountVector c i) = k := c.property

theorem naturalCountVector_injective (k : ℕ) :
    Function.Injective (naturalCountVector : countFiber ι k k → ι → ℕ) := by
  intro c d h
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun h i)

def naturalCountState (k : ℕ) (c : ι → ℕ) (hc : ∑ i, c i = k) : countFiber ι k k :=
  ⟨fun i => ⟨c i, by
    have hh := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq hc
    omega⟩, hc⟩

@[simp] theorem naturalCountVector_state (k : ℕ) (c : ι → ℕ) (hc : ∑ i, c i = k) :
    naturalCountVector (naturalCountState k c hc) = c := rfl

def naturalMultinomialMass (p : ι → ℝ) (k : ℕ) (c : ι → ℕ) : ℝ :=
  if ∑ i, c i = k then (k.factorial : ℝ)*∏ i, p i^(c i)/(c i).factorial else 0

def naturalMultinomialPMF (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) : PMF (ι → ℕ) := (multinomialPMF p hp hpsum k).map naturalCountVector

theorem naturalMultinomialMass_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) (c : ι → ℕ) : 0 ≤ naturalMultinomialMass p k c := by
  unfold naturalMultinomialMass
  split_ifs
  · apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg (fun i _ => div_nonneg (pow_nonneg (hp i) _) (by positivity))
  · exact le_rfl

theorem naturalMultinomialPMF_apply (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (c : ι → ℕ) :
    naturalMultinomialPMF p hp hpsum k c = ENNReal.ofReal (naturalMultinomialMass p k c) := by
  classical
  rw [naturalMultinomialPMF, PMF.map_apply, tsum_fintype]
  by_cases hc : ∑ i, c i = k
  · let d := naturalCountState k c hc
    have hd : naturalCountVector d = c := rfl
    have he (e : countFiber ι k k) : c = naturalCountVector e ↔ e = d := by
      rw [← hd]
      exact (naturalCountVector_injective k).eq_iff.trans eq_comm
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, multinomialPMF_apply,
      naturalMultinomialMass, hc]
    congr 1
  · have he (e : countFiber ι k k) : c ≠ naturalCountVector e := by
      intro hh
      apply hc
      rw [hh]
      exact naturalCountVector_sum e
    simp only [he, if_false, Finset.sum_const_zero, naturalMultinomialMass, hc, ENNReal.ofReal_zero]

theorem naturalMultinomialMass_vector (p : ι → ℝ) (k : ℕ) (c : countFiber ι k k) :
    naturalMultinomialMass p k (naturalCountVector c) = multinomialMass p k c := by
  simp only [naturalMultinomialMass, naturalCountVector_sum, if_true]
  rfl

#print axioms naturalCountVector_sum
#print axioms naturalCountVector_injective
#print axioms naturalCountState
#print axioms naturalCountVector_state
#print axioms naturalMultinomialMass_nonneg
#print axioms naturalMultinomialPMF_apply
#print axioms naturalMultinomialMass_vector

end ConditionalSpectralExtremes.BlockCounts
