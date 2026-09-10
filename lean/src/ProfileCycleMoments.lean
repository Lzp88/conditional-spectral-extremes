import ProfileNormalization

/-! Exact two-distinct-cycle factorial moment from the actual finite law.
The deletion bijection is weighted by an arbitrary residual observable.
No Poisson approximation or factorial-moment identity is assumed. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.ProfileNormalization

theorem cycle_deletion_weighted (θ : ℝ) {N r : ℕ} (j : Fin N)
    (hjr : j.val+1 ≤ r) (hrN : r ≤ N) (G : Configuration N → ℝ) :
    (∑ c ∈ Finset.univ.filter
        (fun c : Configuration N => totalSize c = r ∧ 0 < (c j).val),
      ((((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c) * G (decrement c j)) =
    θ * ∑ d ∈ Finset.univ.filter (fun d : Configuration N => totalSize d = r-(j.val+1)),
      ewensProfileWeight θ d * G d := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun c _ => decrement c j)
  · intro c hc
    obtain ⟨_, hsize, hpos⟩ := Finset.mem_filter.mp hc
    have ht := totalSize_decrement c j hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro c hc d hd he
    exact decrement_injective_on_positive j (Finset.mem_filter.mp hc).2.2
      (Finset.mem_filter.mp hd).2.2 he
  · intro d hd
    have hs : totalSize d = r-(j.val+1) := (Finset.mem_filter.mp hd).2
    have hdN : (d j).val < N := by
      have hc := count_le_size d j
      omega
    refine ⟨increment d j hdN, ?_, decrement_increment d j hdN⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [totalSize_increment, hs]
      omega
    · simp [increment]
  · intro c hc
    rw [ewensProfileWeight_decrement θ c j (Finset.mem_filter.mp hc).2.2]
    ring

def crossMass (θ : ℝ) (N r : ℕ) (j l : Fin N) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Configuration N => totalSize c = r),
    ((c j).val : ℝ) * (c l).val * ewensProfileWeight θ c

theorem crossMass_delete (θ : ℝ) {N r : ℕ} (j l : Fin N) (hjl : j ≠ l)
    (hlen : (j.val+1) + (l.val+1) ≤ r) (hrN : r ≤ N) :
    ((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ) * crossMass θ N r j l =
      θ^2 * massAt θ N (r-((j.val+1)+(l.val+1))) := by
  classical
  calc
    ((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ) * crossMass θ N r j l =
      ∑ c ∈ Finset.univ.filter
        (fun c : Configuration N => totalSize c = r ∧ 0 < (c j).val),
        ((((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c) *
          (((l.val+1 : ℕ) : ℝ) * (decrement c j l).val) := by
      unfold crossMass
      rw [Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hs : totalSize c = r
      · by_cases hp : 0 < (c j).val
        · simp only [hs, hp, and_self, if_true, decrement,
            Function.update_of_ne (Ne.symm hjl)]
          ring
        · have hz : (c j).val = 0 := by omega
          simp [hs, hz]
      · simp [hs]
    _ = θ * ∑ d ∈ Finset.univ.filter
        (fun d : Configuration N => totalSize d = r-(j.val+1)),
        ewensProfileWeight θ d * (((l.val+1 : ℕ) : ℝ) * (d l).val) :=
      cycle_deletion_weighted θ j (by omega) hrN
        (fun d => ((l.val+1 : ℕ) : ℝ) * (d l).val)
    _ = θ * pointedMass θ N (r-(j.val+1)) l := by
      rw [pointedMass_eq_all]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = θ * (θ * massAt θ N ((r-(j.val+1))-(l.val+1))) := by
      rw [pointedMass_delete θ l (by omega) (by omega)]
    _ = θ^2 * massAt θ N (r-((j.val+1)+(l.val+1))) := by
      rw [Nat.sub_sub]
      ring

def crossCoefficient (n k : ℕ) (j l : Fin n) : ℝ :=
  ∑ c : Configuration n,
    if Valid k c then ((c j).val : ℝ) * (c l).val * profileWeight c else 0

def conditionalCycleCrossMoment (n k : ℕ) (j l : Fin n) : ℝ :=
  crossCoefficient n k j l / coefficient n k

def crossPolynomial (n : ℕ) (j l : Fin n) : Polynomial ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Configuration n => totalSize c = n),
    Polynomial.monomial (cycleCount c)
      (((c j).val : ℝ) * (c l).val * profileWeight c)

theorem crossPolynomial_eval (θ : ℝ) (n : ℕ) (j l : Fin n) :
    (crossPolynomial n j l).eval θ = crossMass θ n n j l := by
  simp only [crossPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    crossMass, ewensProfileWeight_factor]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem crossPolynomial_coeff (n k : ℕ) (j l : Fin n) :
    (crossPolynomial n j l).coeff k = crossCoefficient n k j l := by
  unfold crossPolynomial crossCoefficient
  simp only [Polynomial.finsetSum_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hs : totalSize c = n
  · by_cases hk : k = cycleCount c
    · simp [Valid, hs, hk]
    · have hk' : cycleCount c ≠ k := Ne.symm hk
      simp [Valid, hs, hk', Polynomial.coeff_monomial]
  · simp [Valid, hs]

theorem crossPolynomial_identity (n : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (hlen : (j.val+1)+(l.val+1) ≤ n) :
    Polynomial.C (((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ)) * crossPolynomial n j l =
      Polynomial.X^2 * hReal (n-((j.val+1)+(l.val+1))) := by
  apply Polynomial.funext
  intro θ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, crossPolynomial_eval]
  rw [crossMass_delete θ j l hjl hlen le_rfl]
  rw [massAt_eq_hReal_eval θ n _ (Nat.sub_le _ _)]

#print axioms cycle_deletion_weighted
#print axioms crossMass_delete
#print axioms crossPolynomial_identity

theorem crossCoefficient_identity (n k : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (hlen : (j.val+1)+(l.val+1) ≤ n) :
    ((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ) * crossCoefficient n (k+2) j l =
      coefficient (n-((j.val+1)+(l.val+1))) k := by
  have ht := congrArg (fun p : Polynomial ℝ => p.coeff (k+2))
    (crossPolynomial_identity n j l hjl hlen)
  have hcoef : (hReal (n-((j.val+1)+(l.val+1)))).coeff k =
      coefficient (n-((j.val+1)+(l.val+1))) k := by
    rw [coefficient_eq_pochhammer]
    simp [hReal, ConditionalSpectralAudit.CoefficientAlgebra.a]
  simpa only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul,
    crossPolynomial_coeff, hcoef] using ht

/-- Exact two-distinct-cycle conditional factorial moment, indexed by k+2. -/
theorem conditionalCycleCrossMoment_add_two (n k : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (hlen : (j.val+1)+(l.val+1) ≤ n) :
    conditionalCycleCrossMoment n (k+2) j l =
      (1 / (((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ))) *
        (coefficient (n-((j.val+1)+(l.val+1))) k / coefficient n (k+2)) := by
  have ht := crossCoefficient_identity n k j l hjl hlen
  have hd : ((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hv : crossCoefficient n (k+2) j l =
      coefficient (n-((j.val+1)+(l.val+1))) k /
        (((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ)) := by
    apply (eq_div_iff hd).mpr
    nlinarith [ht]
  unfold conditionalCycleCrossMoment
  rw [hv]
  simp only [div_eq_mul_inv]
  ring

/-- Manuscript form E_{n,k}(C_j C_l)=a_{n-j-l,k-2}/(j l a_{n,k}).
    This is derived from the actual finite law, without a Poisson model. -/
theorem conditionalCycleCrossMoment_exact (n k : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (hlen : (j.val+1)+(l.val+1) ≤ n) (hk : 2 ≤ k) :
    conditionalCycleCrossMoment n k j l =
      (1 / (((j.val+1 : ℕ) : ℝ) * ((l.val+1 : ℕ) : ℝ))) *
        (coefficient (n-((j.val+1)+(l.val+1))) (k-2) / coefficient n k) := by
  simpa only [Nat.sub_add_cancel hk] using
    conditionalCycleCrossMoment_add_two n (k-2) j l hjl hlen

/-- The cumulative identity now holds for the actual finite coefficients. -/
theorem finite_cumulative_coefficient_identity (n k : ℕ) :
    (∑ r ∈ Finset.range (n+1), coefficient r k) =
      (n : ℝ) * coefficient n (k+1) + coefficient n k := by
  simp only [coefficient_eq_pochhammer]
  exact_mod_cast ConditionalSpectralAudit.CoefficientAlgebra.cumulative_coefficient_identity n k

#print axioms crossCoefficient_identity
#print axioms conditionalCycleCrossMoment_exact
#print axioms finite_cumulative_coefficient_identity

end ConditionalSpectralExtremes.ProfileNormalization
