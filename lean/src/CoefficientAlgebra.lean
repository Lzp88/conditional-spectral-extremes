import Mathlib

/-!
Universal coefficient algebra used in the paper.

The polynomial h_n is defined explicitly as the normalized ascending
Pochhammer polynomial u(u+1)...(u+n-1)/n!, over the rationals.
This is not a recursive surrogate coefficient array. Both the polynomial
cumulative/shift identities and their coefficient consequence are proved.

The identification of this explicit polynomial with the analytic
coefficient [z^n](1-z)^(-u) is NOT formalized in this file. Neither is its
identification with the finite cycle-profile sum in ManuscriptDefinitions.
No asymptotic estimate or conditional probability theorem is asserted here.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ConditionalSpectralAudit.CoefficientAlgebra

/-- Exact normalized ascending-factorial polynomial h_n(u). -/
def h (n : ℕ) : Polynomial ℚ :=
  C ((n.factorial : ℚ)⁻¹) * ascPochhammer ℚ n

/-- The coefficient a_{n,k} in the explicit normalized polynomial. -/
def a (n k : ℕ) : ℚ := (h n).coeff k

@[simp] theorem h_zero : h 0 = 1 := by simp [h]

/-- Multiplication by n+1 cancels the next factorial denominator. -/
theorem factorial_normalization (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * (((n + 1).factorial : ℚ)⁻¹) =
      ((n.factorial : ℚ)⁻¹) := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hf : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

/-- The exact polynomial recurrence, proved from Pochhammer and factorials. -/
theorem h_recurrence (n : ℕ) :
    C ((n + 1 : ℕ) : ℚ) * h (n + 1) = (X + C (n : ℚ)) * h n := by
  have hp : ascPochhammer ℚ (n + 1) =
      ascPochhammer ℚ n * (X + C (n : ℚ)) := by
    simpa only [C_eq_natCast] using ascPochhammer_succ_right ℚ n
  unfold h
  rw [hp]
  calc
    C ((n + 1 : ℕ) : ℚ) *
        (C (((n + 1).factorial : ℚ)⁻¹) *
          (ascPochhammer ℚ n * (X + C (n : ℚ)))) =
        (C ((n + 1 : ℕ) : ℚ) * C (((n + 1).factorial : ℚ)⁻¹)) *
          (ascPochhammer ℚ n * (X + C (n : ℚ))) := by ring
    _ = C ((n.factorial : ℚ)⁻¹) *
          (ascPochhammer ℚ n * (X + C (n : ℚ))) := by
      rw [← C_mul, factorial_normalization]
    _ = (X + C (n : ℚ)) * (C ((n.factorial : ℚ)⁻¹) * ascPochhammer ℚ n) := by
      ring

/-- The cumulative polynomial identity before canceling u. -/
theorem h_cumulative_mult_X (n : ℕ) :
    X * (∑ r ∈ Finset.range (n + 1), h r) = (X + C (n : ℚ)) * h n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, ← h_recurrence n]
      ring

/-- The polynomial shift identity before canceling u. -/
theorem h_shift_mult_X (n : ℕ) :
    X * (h n).comp (X + 1) = (X + C (n : ℚ)) * h n := by
  have hp : X * (ascPochhammer ℚ n).comp (X + 1) =
      ascPochhammer ℚ n * (X + C (n : ℚ)) := by
    have ht := ascPochhammer_succ_left ℚ n
    rw [ascPochhammer_succ_right] at ht
    simpa only [C_eq_natCast] using ht.symm
  calc
    X * (h n).comp (X + 1) =
        C ((n.factorial : ℚ)⁻¹) * (X * (ascPochhammer ℚ n).comp (X + 1)) := by
      simp only [h, mul_comp, C_comp]
      ring
    _ = C ((n.factorial : ℚ)⁻¹) *
        (ascPochhammer ℚ n * (X + C (n : ℚ))) := by rw [hp]
    _ = (X + C (n : ℚ)) * h n := by unfold h; ring

/-- Source line 1201: sum_{r=0}^n h_r(u) = h_n(u+1). -/
theorem h_cumulative_shift (n : ℕ) :
    (∑ r ∈ Finset.range (n + 1), h r) = (h n).comp (X + 1) := by
  apply mul_left_cancel₀ (show (X : Polynomial ℚ) ≠ 0 by simp)
  rw [h_cumulative_mult_X, h_shift_mult_X]

/-- Source lines 1201--1203, for ALL natural n and k, including n=0:
    sum_{r=0}^n a_{r,k} = n a_{n,k+1} + a_{n,k}. -/
theorem cumulative_coefficient_identity (n k : ℕ) :
    (∑ r ∈ Finset.range (n + 1), a r k) =
      (n : ℚ) * a n (k + 1) + a n k := by
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff (k + 1))
    (h_cumulative_mult_X n)
  simpa only [a, add_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    finsetSum_coeff, add_comm] using hc

#print axioms h_zero
#print axioms factorial_normalization
#print axioms h_recurrence
#print axioms h_cumulative_mult_X
#print axioms h_shift_mult_X
#print axioms h_cumulative_shift
#print axioms cumulative_coefficient_identity

end ConditionalSpectralAudit.CoefficientAlgebra
