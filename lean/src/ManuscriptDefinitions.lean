import Mathlib

/-!
Finite definitions for Sections 1 and 6 of the paper.

IMPORTANT: `ExactCycleLocalization` is a proposition DEFINITION, not a theorem.
Its successful elaboration is NOT a proof of localization. No analytic or
probabilistic assertion from the paper is inserted as an axiom here.

Configurations use Fin (n+1) counts: every genuine size-n cycle profile has
each count <= n, so this is an exact finite encoding of the paper's state
space. The validity predicate imposes BOTH the size and the cycle count.
The polynomial norm is defined before taking its logarithm. In particular,
the definition never substitutes Lean's totalized log 0 for a -infinity
height at a root of a characteristic polynomial.
-/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes

abbrev Configuration (n : ℕ) := Fin n → Fin (n + 1)

def totalSize {n : ℕ} (c : Configuration n) : ℕ :=
  ∑ j : Fin n, (j.val + 1) * (c j).val

def cycleCount {n : ℕ} (c : Configuration n) : ℕ :=
  ∑ j : Fin n, (c j).val

def Valid {n : ℕ} (k : ℕ) (c : Configuration n) : Prop :=
  totalSize c = n ∧ cycleCount c = k

def profileWeight {n : ℕ} (c : Configuration n) : ℝ :=
  ∏ j : Fin n, ((j.val + 1 : ℕ) : ℝ)⁻¹ ^ (c j).val /
    (Nat.factorial (c j).val : ℝ)

def coefficient (n k : ℕ) : ℝ := by
  classical
  exact ∑ c : Configuration n, if Valid k c then profileWeight c else 0

def conditionalProbability (n k : ℕ) (event : Configuration n → Prop) : ℝ := by
  classical
  exact (∑ c : Configuration n,
    if Valid k c ∧ event c then profileWeight c else 0) / coefficient n k

def characteristicPolynomial {n : ℕ} (c : Configuration n) : Polynomial ℂ :=
  ∏ j : Fin n, (1 - Polynomial.X ^ (j.val + 1)) ^ (c j).val

def circleNorm (p : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ r = ‖p.eval z‖}

def maximumLogModulus {n : ℕ} (c : Configuration n) : ℝ :=
  Real.log (circleNorm (characteristicPolynomial c))

def lambda (s : ℝ) : ℝ :=
  Real.log (Real.Gamma (1 + s)) - 2 * Real.log (Real.Gamma (1 + s / 2))

def center (n k : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ s : ℝ, 0 < s ∧
    r = (Real.log (n : ℝ) + (k : ℝ) * lambda s) / s}

/-- Theorem 1.1 as a fully quantified proposition, WITHOUT a proof.
Uniform epsilon-N formulation of the supremum tending to zero.
All k are natural numbers, exactly as the feasible cycle counts for
sufficiently large n in any fixed positive compact k/log n interval.
-/
def ExactCycleLocalization : Prop :=
  ∀ κlo κhi : ℝ, 0 < κlo → κlo < κhi →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
        κlo * Real.log (n : ℝ) ≤ (k : ℝ) →
        (k : ℝ) ≤ κhi * Real.log (n : ℝ) →
        conditionalProbability n k (fun c =>
          |maximumLogModulus c - center n k| >
            C * Real.log (Real.log (n : ℝ))) < ε

theorem profileWeight_pos {n : ℕ} (c : Configuration n) :
    0 < profileWeight c := by
  unfold profileWeight
  apply Finset.prod_pos
  intro j _
  positivity

theorem characteristicPolynomial_eval_zero {n : ℕ} (c : Configuration n) :
    (characteristicPolynomial c).eval 0 = 1 := by
  classical
  simp [characteristicPolynomial, Polynomial.eval_prod]

theorem characteristicPolynomial_ne_zero {n : ℕ} (c : Configuration n) :
    characteristicPolynomial c ≠ 0 := by
  intro h
  have := characteristicPolynomial_eval_zero c
  rw [h] at this
  simp at this

/-- The finite coefficient is nonnegative, with no feasibility assumption. -/
theorem coefficient_nonneg (n k : ℕ) : 0 ≤ coefficient n k := by
  classical
  unfold coefficient
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact le_of_lt (profileWeight_pos c)
  · exact le_rfl

/-- Positive mass is required before normalizing to a probability law. -/
theorem coefficient_pos_of_valid {n k : ℕ} (c : Configuration n) (hc : Valid k c) :
    0 < coefficient n k := by
  classical
  unfold coefficient
  apply Finset.sum_pos'
  · intro d _
    split_ifs
    · exact le_of_lt (profileWeight_pos d)
    · exact le_rfl
  · exact ⟨c, Finset.mem_univ c, by simpa [hc] using profileWeight_pos c⟩

theorem conditionalProbability_univ (n k : ℕ) (h : coefficient n k ≠ 0) :
    conditionalProbability n k (fun _ => True) = 1 := by
  classical
  simp only [conditionalProbability, and_true]
  change coefficient n k / coefficient n k = 1
  exact div_self h

theorem conditionalProbability_bounds (n k : ℕ) (event : Configuration n → Prop)
    (h : 0 < coefficient n k) :
    0 ≤ conditionalProbability n k event ∧ conditionalProbability n k event ≤ 1 := by
  classical
  have hn : 0 ≤ ∑ c : Configuration n,
      if Valid k c ∧ event c then profileWeight c else 0 := by
    apply Finset.sum_nonneg
    intro c _
    split_ifs
    · exact le_of_lt (profileWeight_pos c)
    · exact le_rfl
  have hu : (∑ c : Configuration n,
      if Valid k c ∧ event c then profileWeight c else 0) ≤ coefficient n k := by
    unfold coefficient
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : Valid k c
    · simp only [hc, true_and, if_true]
      split_ifs
      · exact le_rfl
      · exact le_of_lt (profileWeight_pos c)
    · simp [hc]
  unfold conditionalProbability
  exact ⟨div_nonneg hn h.le, (div_le_one h).2 hu⟩

#print axioms profileWeight_pos
#print axioms characteristicPolynomial_eval_zero
#print axioms characteristicPolynomial_ne_zero
#print axioms coefficient_nonneg
#print axioms coefficient_pos_of_valid
#print axioms conditionalProbability_univ
#print axioms conditionalProbability_bounds
#check ExactCycleLocalization

end ConditionalSpectralExtremes
