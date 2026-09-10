import ProfileNormalizationRecurrence
import CoefficientAlgebra

/-!
Exact normalization bridge for the ACTUAL manuscript configuration sum.
The proof uses the coordinate deletion recurrence proved in the imported
helper, compares it with the explicit Pochhammer recurrence, and extracts
coefficients from the full profile generating polynomial.
No normalization identity is a hypothesis; the final identity is a theorem.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.ProfileNormalization

open ConditionalSpectralAudit.CoefficientAlgebra

def hReal (n : ℕ) : Polynomial ℝ := (h n).map (algebraMap ℚ ℝ)

theorem hReal_eval_recurrence (θ : ℝ) (m : ℕ) :
    ((m+1 : ℕ) : ℝ) * (hReal (m+1)).eval θ =
      θ * ∑ q ∈ Finset.range (m+1), (hReal q).eval θ := by
  have hp : Polynomial.C ((m+1 : ℕ) : ℚ) * h (m+1) =
      Polynomial.X * (∑ q ∈ Finset.range (m+1), h q) :=
    (h_recurrence m).trans (h_cumulative_mult_X m).symm
  have he := congrArg (fun p : Polynomial ℚ => p.eval₂ (algebraMap ℚ ℝ) θ) hp
  simpa [hReal, Polynomial.eval_map, Polynomial.eval₂_finsetSum] using he

/-- Equality for every size up to the fixed ambient configuration bound. -/
theorem massAt_eq_hReal_eval (θ : ℝ) (N r : ℕ) (hrN : r ≤ N) :
    massAt θ N r = (hReal r).eval θ := by
  revert hrN
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hrN
    cases r with
    | zero => simp [massAt_zero, hReal]
    | succ m =>
      have hn : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      rw [massAt_recurrence θ hrN, hReal_eval_recurrence]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      have hlt : q < m+1 := Finset.mem_range.mp hq
      exact ih q hlt (le_trans (Nat.le_of_lt hlt) hrN)

/-- The actual size-n profile generating polynomial with cycle marker X. -/
def profilePolynomial (n : ℕ) : Polynomial ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Configuration n => totalSize c = n),
    Polynomial.C (profileWeight c) * Polynomial.X ^ cycleCount c

theorem profilePolynomial_eval (θ : ℝ) (n : ℕ) :
    (profilePolynomial n).eval θ = massAt θ n n := by
  classical
  simp only [profilePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    massAt, ewensProfileWeight_factor]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The complete finite profile polynomial is the normalized Pochhammer polynomial. -/
theorem profilePolynomial_eq_hReal (n : ℕ) : profilePolynomial n = hReal n := by
  apply Polynomial.funext
  intro θ
  rw [profilePolynomial_eval, massAt_eq_hReal_eval θ n n le_rfl]

/-- Marker extraction recovers the exact pre-existing finite coefficient. -/
theorem profilePolynomial_coeff (n k : ℕ) :
    (profilePolynomial n).coeff k = coefficient n k := by
  classical
  unfold profilePolynomial coefficient
  simp only [Polynomial.finsetSum_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hs : totalSize c = n
  · by_cases hk : k = cycleCount c
    · simp [Valid, hs, hk]
    · have hkn : cycleCount c ≠ k := Ne.symm hk
      simp [Valid, hs, hk, hkn]
  · simp [Valid, hs]

/-- The requested bridge: literal finite profile sum = literal Pochhammer coefficient.
    All n,k are covered, including impossible indices and n=0. -/
theorem coefficient_eq_pochhammer (n k : ℕ) :
    coefficient n k = (ConditionalSpectralAudit.CoefficientAlgebra.a n k : ℝ) := by
  rw [← profilePolynomial_coeff, profilePolynomial_eq_hReal]
  simp [hReal, ConditionalSpectralAudit.CoefficientAlgebra.a]

/-- Ordinary finite Ewens normalization, proved rather than postulated. -/
theorem ewensPartition_eq_hReal_eval (θ : ℝ) (n : ℕ) :
    ewensPartition θ n = (hReal n).eval θ := by
  have hm : ewensPartition θ n = massAt θ n n := by
    simp [ewensPartition, ewensMass, massAt, Finset.sum_filter]
  rw [hm, massAt_eq_hReal_eval θ n n le_rfl]

#print axioms hReal_eval_recurrence
#print axioms massAt_eq_hReal_eval
#print axioms profilePolynomial_eq_hReal
#print axioms profilePolynomial_coeff
#print axioms coefficient_eq_pochhammer
#print axioms ewensPartition_eq_hReal_eval

end ConditionalSpectralExtremes.ProfileNormalization
