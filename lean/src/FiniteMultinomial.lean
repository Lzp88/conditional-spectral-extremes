import FiniteBlockWeights

/-! A finite multinomial probability mass function and its actual generating
function, obtained from exact factorial enumeration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts

variable {ι : Type*} [Fintype ι]

def multinomialMass (p : ι → ℝ) (k : ℕ) (c : countFiber ι k k) : ℝ :=
  (k.factorial : ℝ) * boundedWeight p c.val

theorem multinomialMass_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) (c : countFiber ι k k) : 0 ≤ multinomialMass p k c := by
  unfold multinomialMass boundedWeight
  apply mul_nonneg (by positivity)
  exact Finset.prod_nonneg (fun i _ => div_nonneg (pow_nonneg (hp i) _) (by positivity))

theorem multinomialMass_sum (p : ι → ℝ) (k : ℕ) :
    (∑ c, multinomialMass p k c) = (∑ i, p i)^k := by
  unfold multinomialMass
  rw [← Finset.mul_sum, boundedWeight_sum_fixed_count p k k le_rfl]
  field_simp

theorem multinomialMass_sum_one (p : ι → ℝ) (hp : ∑ i, p i = 1) (k : ℕ) :
    (∑ c, multinomialMass p k c) = 1 := by rw [multinomialMass_sum, hp, one_pow]

/-- The actual normalized multinomial law on finite count vectors summing to k. -/
def multinomialPMF (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) : PMF (countFiber ι k k) :=
  PMF.ofFintype (fun c => ENNReal.ofReal (multinomialMass p k c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => multinomialMass_nonneg hp k c),
      multinomialMass_sum_one p hpsum k, ENNReal.ofReal_one])

theorem multinomialPMF_apply (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (c : countFiber ι k k) :
    multinomialPMF p hp hpsum k c = ENNReal.ofReal (multinomialMass p k c) := rfl

theorem boundedWeight_mul (p z : ι → ℝ) {n : ℕ} (c : ι → Fin (n+1)) :
    boundedWeight (fun i => p i*z i) c = boundedWeight p c * ∏ i, z i^(c i).val := by
  unfold boundedWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_pow]
  ring

/-- Exact multivariate probability generating function, proved from the
    finite mass function rather than assumed independence of the counts. -/
theorem multinomial_generating_function (p z : ι → ℝ) (k : ℕ) :
    (∑ c : countFiber ι k k, multinomialMass p k c * ∏ i, z i^(c.val i).val) =
      (∑ i, p i*z i)^k := by
  rw [← multinomialMass_sum (fun i => p i*z i) k]
  apply Finset.sum_congr rfl
  intro c _
  unfold multinomialMass
  rw [boundedWeight_mul]
  ring

theorem multinomial_mgf (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) (t : ℝ) :
    (∑ c : countFiber ι k k,
      multinomialMass p k c * Real.exp (t*((c.val j).val : ℝ))) =
      (1-p j+p j*Real.exp t)^k := by
  classical
  have hp : ∑ i, p i * (if i = j then Real.exp t else 1) = 1-p j+p j*Real.exp t := by
    calc
      _ = ∑ i, (p i + if i = j then p j*(Real.exp t-1) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = j
        · simp [hi]
          ring
        · simp [hi]
      _ = _ := by rw [Finset.sum_add_distrib, hpsum]; simp; ring
  have hh := multinomial_generating_function p (fun i => if i = j then Real.exp t else 1) k
  rw [hp] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ite_pow, one_pow]
  rw [Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true, ← Real.exp_nat_mul]
  congr 1
  ring

def multinomialProbability (p : ι → ℝ) (k : ℕ) (A : countFiber ι k k → Prop) : ℝ :=
  ∑ c, if A c then multinomialMass p k c else 0

/-- Chernoff's exponential bound for one actual multinomial coordinate. -/
theorem multinomial_upper_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι) (r t : ℝ) (ht : 0 ≤ t) :
    multinomialProbability p k (fun c => r ≤ ((c.val j).val : ℝ)) ≤
      Real.exp (-t*r) * (1-p j+p j*Real.exp t)^k := by
  rw [← multinomial_mgf p hpsum k j t, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hm := multinomialMass_nonneg hp k c
  by_cases hc : r ≤ ((c.val j).val : ℝ)
  · simp only [hc, if_true]
    have he : 1 ≤ Real.exp (-t*r) * Real.exp (t*((c.val j).val : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    nlinarith
  · simp only [hc, if_false]
    positivity

#print axioms multinomialMass_nonneg
#print axioms multinomialMass_sum
#print axioms multinomialMass_sum_one
#print axioms multinomialPMF
#print axioms multinomialPMF_apply
#print axioms boundedWeight_mul
#print axioms multinomial_generating_function
#print axioms multinomial_mgf
#print axioms multinomial_upper_chernoff

end ConditionalSpectralExtremes.BlockCounts
