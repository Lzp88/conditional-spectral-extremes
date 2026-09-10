import Mathlib

/-!
Checked deterministic algebra used in Section 3 of
the paper.

These universally quantified identities concern the actual frontier,
sample-count chord, energy, and box-width cancellation formulas.
They do NOT prove the bridge density estimate, existence of the regular
environment, construction of the dyadic partition, or Lemma 3.4 itself.
In particular the analytic critical equation is an explicit hypothesis,
not an axiom or a theorem asserted without proof.
-/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralAudit.BoxAlgebra

/-- Manuscript (3.11): the frontier at spatial coordinate a and count S. -/
def frontier (a lam S s : ℝ) : ℝ := (a + lam * S) / s

/-- A point in the box centered gamma below the frontier. -/
def boxPoint (a lam S s gamma err : ℝ) : ℝ :=
  frontier a lam S s - gamma + err

/-- Exact box drift (source lines 655--657). -/
theorem box_drift
    (a S H q lam s mu kappa gamma0 gamma1 err0 err1 : ℝ)
    (hs : s ≠ 0) (hkappa : kappa ≠ 0)
    (hcritical : s * mu - lam = 1 / kappa) :
    boxPoint (a + H) lam (S + q) s gamma1 err1 -
        boxPoint a lam S s gamma0 err0 - q * mu =
      (H - q / kappa) / s - (gamma1 - gamma0) + (err1 - err0) := by
  have hlam : lam = s * mu - 1 / kappa := by linarith
  unfold boxPoint frontier
  rw [hlam]
  field_simp [hs, hkappa]
  ring

/-- Exact gap between the frontier and the sample-count chord
    (source lines 683--684). No critical equation is needed. -/
theorem chord_gap
    (a0 S0 a H t q lam s gamma0 gamma1 err0 err1 : ℝ)
    (hs : s ≠ 0) (hq : q ≠ 0) :
    frontier (a0 + a) lam (S0 + t) s -
        ((1 - t / q) * boxPoint a0 lam S0 s gamma0 err0 +
          (t / q) * boxPoint (a0 + H) lam (S0 + q) s gamma1 err1) =
      (1 - t / q) * (gamma0 - err0) + (t / q) * (gamma1 - err1) +
        (a - (t / q) * H) / s := by
  unfold boxPoint frontier
  field_simp [hs, hq]
  ring

/-- The discrepancy numerator in source line 689. -/
theorem discrepancy_interpolation
    (a H t q kappa D_i D_end : ℝ) (hq : q ≠ 0)
    (hi : t = kappa * a + D_i) (hend : q = kappa * H + D_end) :
    a - (t / q) * H = (a * D_end - H * D_i) / q := by
  field_simp [hq]
  rw [hi, hend]
  ring

/-- The final box center is exactly frontier minus its prescribed gap. -/
theorem terminal_gap (a r lam Q s : ℝ) (hs : s ≠ 0) :
    (a - r + lam * Q) / s + 1 / 2 =
      frontier a lam Q s - (r / s - 1 / 2) := by
  unfold frontier
  field_simp [hs]
  ring

/-- The terminal height interval is compatible with the last barrier as
    soon as the deterministic initial gap exceeds G+1. -/
theorem terminal_window_compatible
    (a r lam Q s G : ℝ) (hs : s ≠ 0) (hgap : G + 1 ≤ r / s) :
    (a - r + lam * Q) / s + 1 ≤ frontier a lam Q s - G := by
  have hid : frontier a lam Q s - (a - r + lam * Q) / s = r / s := by
    unfold frontier
    field_simp [hs]
    ring
  linarith

/-- Quantitative energy inequality for the five terms in U_j. -/
theorem five_term_square (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤
      5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
    sq_nonneg (d - e)]

/-- Summing the actual U_j algebra. P and N are the neighboring E terms,
    and R is r/sqrt(H_j) on the two boundary groups and zero elsewhere. -/
theorem summed_box_energy
    {ι : Type*} [Fintype ι] (P E N R : ι → ℝ) :
    (∑ i, (1 + P i + E i + N i + R i) ^ 2) ≤
      5 * ((Fintype.card ι : ℝ) + (∑ i, (P i) ^ 2) +
        (∑ i, (E i) ^ 2) + (∑ i, (N i) ^ 2) + (∑ i, (R i) ^ 2)) := by
  calc
    (∑ i, (1 + P i + E i + N i + R i) ^ 2) ≤
        ∑ i, 5 * (1 ^ 2 + (P i) ^ 2 + (E i) ^ 2 +
          (N i) ^ 2 + (R i) ^ 2) :=
      Finset.sum_le_sum fun i _ => five_term_square 1 (P i) (E i) (N i) (R i)
    _ = 5 * ((Fintype.card ι : ℝ) + (∑ i, (P i) ^ 2) +
        (∑ i, (E i) ^ 2) + (∑ i, (N i) ^ 2) + (∑ i, (R i) ^ 2)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_add_distrib, one_pow,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The resulting linear-in-number-of-groups bound, once the three
    environmental energies and the two boundary costs have been bounded. -/
theorem box_energy_from_environment
    {ι : Type*} [Fintype ι] (P E N R : ι → ℝ) (CE bcost : ℝ)
    (hP : (∑ i, (P i) ^ 2) ≤ CE * (Fintype.card ι : ℝ))
    (hE : (∑ i, (E i) ^ 2) ≤ CE * (Fintype.card ι : ℝ))
    (hN : (∑ i, (N i) ^ 2) ≤ CE * (Fintype.card ι : ℝ))
    (hR : (∑ i, (R i) ^ 2) ≤ bcost) :
    (∑ i, (1 + P i + E i + N i + R i) ^ 2) ≤
      5 * ((1 + 3 * CE) * (Fintype.card ι : ℝ) + bcost) := by
  have h := summed_box_energy P E N R
  nlinarith

/-- Exact cancellation of all intermediate endpoint widths. There are
    n+1 group kernels and n intermediate boxes. w_i is sqrt(H_i).
    A terminal interval of width delta multiplies both sides by delta. -/
theorem endpoint_width_cancellation
    (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∏ i ∈ Finset.range (n + 1), (w i)⁻¹) *
        (∏ i ∈ Finset.range n, 2 * w i) =
      (2 : ℝ) ^ n / w n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ (fun i => (w i)⁻¹),
        Finset.prod_range_succ (fun i => 2 * w i)]
      calc
        ((∏ i ∈ Finset.range (n + 1), (w i)⁻¹) * (w (n + 1))⁻¹) *
            ((∏ i ∈ Finset.range n, 2 * w i) * (2 * w n)) =
            ((∏ i ∈ Finset.range (n + 1), (w i)⁻¹) *
              (∏ i ∈ Finset.range n, 2 * w i)) *
                (2 * w n * (w (n + 1))⁻¹) := by ring
        _ = (2 : ℝ) ^ n / w n * (2 * w n * (w (n + 1))⁻¹) := by rw [ih]
        _ = (2 : ℝ) ^ (n + 1) / w (n + 1) := by
          rw [pow_succ]
          field_simp [hw n, hw (n + 1)]

/-- The cancellation as stated with the manuscript's sqrt(H) scales. -/
theorem sqrt_endpoint_width_cancellation
    (n : ℕ) (H : ℕ → ℝ) (hH : ∀ i, 0 < H i) :
    (∏ i ∈ Finset.range (n + 1), (Real.sqrt (H i))⁻¹) *
        (∏ i ∈ Finset.range n, 2 * Real.sqrt (H i)) =
      (2 : ℝ) ^ n / Real.sqrt (H n) := by
  apply endpoint_width_cancellation
  intro i
  exact ne_of_gt (Real.sqrt_pos.2 (hH i))

#print axioms box_drift
#print axioms chord_gap
#print axioms discrepancy_interpolation
#print axioms terminal_gap
#print axioms terminal_window_compatible
#print axioms five_term_square
#print axioms summed_box_energy
#print axioms box_energy_from_environment
#print axioms endpoint_width_cancellation
#print axioms sqrt_endpoint_width_cancellation

end ConditionalSpectralAudit.BoxAlgebra
