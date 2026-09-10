import NaturalMultinomialLaw
import PoissonExponentialFactorial

/-! Actual Poissonization: mixing the actual multinomial laws with a
Poisson sample size gives the product of the actual Poisson count laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def poissonMultinomialMixture (r : ℝ≥0) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) : PMF (ι → ℕ) :=
  (poissonMeasure r).toPMF.bind (fun n => naturalMultinomialPMF p hp hpsum n)

def independentPoissonCountLaw (r : ℝ≥0) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure ⟨(r : ℝ)*p i, mul_nonneg r.coe_nonneg (hp i)⟩)

instance independentPoissonCountLaw_probability (r : ℝ≥0) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    IsProbabilityMeasure (independentPoissonCountLaw r p hp) := by
  unfold independentPoissonCountLaw
  infer_instance

theorem poissonMultinomialMixture_apply (r : ℝ≥0) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (c : ι → ℕ) :
    poissonMultinomialMixture r p hp hpsum c = ENNReal.ofReal
      (Real.exp (-(r : ℝ))*(r : ℝ)^(∑ i, c i)*∏ i, p i^(c i)/(c i).factorial) := by
  classical
  rw [poissonMultinomialMixture, PMF.bind_apply]
  simp_rw [Measure.toPMF_apply, poissonMeasure_singleton, naturalMultinomialPMF_apply]
  have he (n : ℕ) : ENNReal.ofReal (Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ))*
      ENNReal.ofReal (naturalMultinomialMass p n c) =
      if ∑ i, c i = n then ENNReal.ofReal
        (Real.exp (-(r : ℝ))*(r : ℝ)^n*∏ i, p i^(c i)/(c i).factorial) else 0 := by
    by_cases hn : ∑ i, c i = n
    · rw [naturalMultinomialMass, if_pos hn, if_pos hn,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ))]
      congr 1
      field_simp
    · simp only [naturalMultinomialMass, hn, if_false, ENNReal.ofReal_zero, mul_zero]
  simp_rw [he]
  simp

theorem poisson_count_mass_factorization (r : ℝ≥0) (p : ι → ℝ)
    (hpsum : ∑ i, p i = 1) (c : ι → ℕ) :
    Real.exp (-(r : ℝ))*(r : ℝ)^(∑ i, c i)*∏ i, p i^(c i)/(c i).factorial =
      ∏ i, (Real.exp (-((r : ℝ)*p i))*((r : ℝ)*p i)^(c i)/(c i).factorial) := by
  have he : (∏ i, Real.exp (-((r : ℝ)*p i))) = Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hpsum, mul_one]
  have hp : (∏ i, ((r : ℝ)*p i)^(c i)) = (r : ℝ)^(∑ i, c i)*(∏ i, p i^(c i)) := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_mul_distrib, he, hp]
  ring

theorem poissonMultinomialMixture_eq_independent (r : ℝ≥0) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    poissonMultinomialMixture r p hp hpsum = (independentPoissonCountLaw r p hp).toPMF := by
  classical
  ext c
  rw [poissonMultinomialMixture_apply, Measure.toPMF_apply, independentPoissonCountLaw, Measure.pi_singleton]
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i (_ : i ∈ Finset.univ) => by
    have hi := hp i
    positivity)]
  congr 1
  exact poisson_count_mass_factorization r p hpsum c

#print axioms poissonMultinomialMixture_apply
#print axioms poisson_count_mass_factorization
#print axioms poissonMultinomialMixture_eq_independent

end ConditionalSpectralExtremes.BlockCounts
