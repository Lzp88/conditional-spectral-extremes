import ActualReservoirGamma

/-! Explicit domination of every fixed logarithmic power by the reservoir's outer exponential. -/
noncomputable section
namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem log_quartic_exponential_bound {P x : ℝ} (q : ℕ)
    (hx : 1 ≤ x) (hlarge : 4 * (P + q + 2) ≤ x) :
    Real.exp ((P + 1) * x) * x ^ q * Real.exp (-x ^ 4 / 4) ≤ Real.exp (-x) := by
  have hxp : 0 ≤ x := zero_le_one.trans hx
  have hxexp : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpow : x ^ q ≤ Real.exp ((q : ℝ) * x) := by
    have hh := pow_le_pow_left₀ hxp hxexp q
    simpa only [← Real.exp_nat_mul] using hh
  have hsq : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hlarge hxp
  have hexp : (P + 1) * x + (q : ℝ) * x + (-x ^ 4 / 4) ≤ -x := by nlinarith
  calc
    _ ≤ Real.exp ((P + 1) * x) * Real.exp ((q : ℝ) * x) * Real.exp (-x ^ 4 / 4) := by gcongr
    _ = Real.exp ((P + 1) * x + (q : ℝ) * x + (-x ^ 4 / 4)) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

theorem reservoir_outer_decay_bound {M : ℝ} (hM : 0 ≤ M) {n b N : ℕ}
    (hn : 2 ≤ n) (hb : 0 < b) (hbN : b ≤ n) (hNn : N ≤ n) (hnN : n ≤ 2 * N)
    (hcut : (b : ℝ) ≤ (n : ℝ) / (Real.log n) ^ 4) (q : ℕ)
    (hL : 1 ≤ Real.log n)
    (hlarge : 4 * (reservoirOuterPower M + q + 2) ≤ Real.log n) :
    (N : ℝ) * reservoirOuterError M b N * (Real.log n) ^ q ≤
      (2 * Real.pi * reservoirOuterConstant M) / n := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbp : 0 < (b : ℝ) := by exact_mod_cast hb
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hL
  have hP : 0 ≤ reservoirOuterPower M := by unfold reservoirOuterPower; positivity
  have hbpow : (b : ℝ) ^ reservoirOuterPower M ≤ (n : ℝ) ^ reservoirOuterPower M :=
    Real.rpow_le_rpow hbp.le (by exact_mod_cast hbN) hP
  have hmass : (b : ℝ) * (Real.log n) ^ 4 ≤ n := (le_div_iff₀ (pow_pos hLp 4)).1 hcut
  have hnNr : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnN
  have hbank : -(N : ℝ) / (2 * b) ≤ -(Real.log n) ^ 4 / 4 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b) (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hmain : (n : ℝ) * (n : ℝ) ^ reservoirOuterPower M =
      Real.exp ((reservoirOuterPower M + 1) * Real.log n) := by
    rw [Real.rpow_def_of_pos hnp]
    nth_rw 1 [← Real.exp_log hnp]
    rw [← Real.exp_add]
    congr 1
    ring
  have hK : 0 ≤ 2 * Real.pi * reservoirOuterConstant M := by
    have := reservoirOuterConstant_pos M
    positivity
  calc
    _ = (2 * Real.pi * reservoirOuterConstant M) * ((N : ℝ) * (b : ℝ) ^ reservoirOuterPower M) *
        (Real.log n) ^ q * Real.exp (-(N : ℝ) / (2 * b)) := by unfold reservoirOuterError; ring
    _ ≤ (2 * Real.pi * reservoirOuterConstant M) * ((n : ℝ) * (n : ℝ) ^ reservoirOuterPower M) *
        (Real.log n) ^ q * Real.exp (-(Real.log n) ^ 4 / 4) := by
      gcongr
    _ = (2 * Real.pi * reservoirOuterConstant M) *
        (Real.exp ((reservoirOuterPower M + 1) * Real.log n) * (Real.log n) ^ q *
          Real.exp (-(Real.log n) ^ 4 / 4)) := by rw [hmain]; ring
    _ ≤ (2 * Real.pi * reservoirOuterConstant M) * Real.exp (-Real.log n) :=
      mul_le_mul_of_nonneg_left (log_quartic_exponential_bound q hL hlarge) hK
    _ = _ := by rw [Real.exp_neg, Real.exp_log hnp]; ring

#print axioms reservoir_outer_decay_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
