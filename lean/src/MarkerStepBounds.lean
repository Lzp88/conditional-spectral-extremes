import ComplexCoefficientAnalysis

/-! Uniform actual marker-step remainder bounds, including complex parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis

def markerStepLog (z : ℂ) (n : ℕ) : ℂ :=
  Complex.log (1 + z / n) - z * Complex.log (1 + 1 / (n : ℂ))

theorem norm_log_remainder_half {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hp : 0 < 1 - ‖w‖ := by linarith [norm_nonneg w]
  have hi : (1 - ‖w‖)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ hp (by norm_num)).2
    norm_num
    linarith
  have hh := Complex.norm_log_one_add_sub_self_le (show ‖w‖ < 1 by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖w‖)]

theorem markerStepLog_bound {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    {n : ℕ} (hn : 2 * (R + 1) ≤ n) :
    ‖markerStepLog z n‖ ≤ (R ^ 2 + R) / (n : ℝ) ^ 2 := by
  have hnp : 0 < (n : ℝ) := by linarith
  have hnr : ‖z / (n : ℂ)‖ = ‖z‖ / n := by simp
  have hn1 : ‖(1 : ℂ) / n‖ = 1 / (n : ℝ) := by simp
  have hzhalf : ‖z / (n : ℂ)‖ ≤ 1 / 2 := by rw [hnr]; apply (div_le_iff₀ hnp).2; linarith
  have hnhalf : ‖(1 : ℂ) / n‖ ≤ 1 / 2 := by rw [hn1]; apply (div_le_iff₀ hnp).2; linarith
  have h1 := norm_log_remainder_half hzhalf
  have h2 := norm_log_remainder_half hnhalf
  have he : markerStepLog z n =
      (Complex.log (1 + z / n) - z / n) - z * (Complex.log (1 + 1 / (n : ℂ)) - 1 / n) := by
    unfold markerStepLog
    ring
  rw [hnr] at h1
  rw [hn1] at h2
  calc
    ‖markerStepLog z n‖ ≤ ‖Complex.log (1 + z / n) - z / n‖ +
      ‖z‖ * ‖Complex.log (1 + 1 / (n : ℂ)) - 1 / n‖ := by
        rw [he]
        simpa only [norm_mul] using norm_sub_le
          (Complex.log (1 + z / n) - z / n) (z * (Complex.log (1 + 1 / (n : ℂ)) - 1 / n))
    _ ≤ (‖z‖ / n) ^ 2 + ‖z‖ * (1 / (n : ℝ)) ^ 2 := by gcongr
    _ ≤ (R / n) ^ 2 + R * (1 / (n : ℝ)) ^ 2 := by gcongr
    _ = (R ^ 2 + R) / (n : ℝ) ^ 2 := by ring

theorem markerStepExp_bound {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    {n : ℕ} (hn : 2 * (R + 1) ≤ n) :
    ‖Complex.exp (markerStepLog z n) - 1‖ ≤ 2 * (R ^ 2 + R) / (n : ℝ) ^ 2 := by
  have hnp : 0 < (n : ℝ) := by linarith
  have hs : (R ^ 2 + R) / (n : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hnp)).2
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (R + 1))]
  have hh := Complex.norm_exp_sub_one_le ((markerStepLog_bound hR hz hn).trans hs)
  calc
    ‖Complex.exp (markerStepLog z n) - 1‖ ≤ 2 * ‖markerStepLog z n‖ := hh
    _ ≤ 2 * ((R ^ 2 + R) / (n : ℝ) ^ 2) := by gcongr; exact markerStepLog_bound hR hz hn
    _ = _ := by ring

def normalizedMarker (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z * Complex.log n) * (n : ℂ) * markerValue n z

theorem normalizedMarker_eq {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    normalizedMarker n z = (n : ℂ) ^ (1 - z) * markerValue n z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Complex.cpow_def_of_ne_zero hn0]
  have he : Complex.log (n : ℂ) * (1 - z) = Complex.log n + -z * Complex.log n := by ring
  rw [he, Complex.exp_add, Complex.exp_log hn0]
  unfold normalizedMarker
  ring

theorem normalizedMarker_tendsto (z : ℂ) :
    Tendsto (fun n => normalizedMarker n z) atTop (𝓝 ((Complex.Gamma z)⁻¹)) := by
  by_cases hz : ∀ j : ℕ, z ≠ -j
  · apply (markerValue_pointwise_asymptotic hz).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (normalizedMarker_eq hn z).symm
  · push Not at hz
    obtain ⟨m, rfl⟩ := hz
    simp only [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with n hn
    simp [normalizedMarker, markerValue_eq_asc, ascPochhammer_eval_neg_coe_nat_of_lt hn]

theorem markerValue_step (n : ℕ) (z : ℂ) :
    ((n : ℂ) + 1) * markerValue (n + 1) z = (z + n) * markerValue n z := by
  simp only [markerValue_eq_asc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_natCast]
  field_simp

theorem log_nat_ratio {n : ℕ} (hn : n ≠ 0) :
    Complex.log (1 + 1 / (n : ℂ)) = Complex.log ((n : ℂ) + 1) - Complex.log n := by
  have hnp : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have he : (1 : ℝ) + 1 / n = ((n : ℝ) + 1) / n := by field_simp
  have hh : Real.log (1 + 1 / (n : ℝ)) = Real.log ((n : ℝ) + 1) - Real.log n := by
    rw [he, Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0) hnp.ne']
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hh
  push_cast at hc
  simpa only [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 1 + 1 / n),
    Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), Complex.natCast_log,
    Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using hc

theorem normalizedMarker_step {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : 1 + z / (n : ℂ) ≠ 0) :
    normalizedMarker (n + 1) z = normalizedMarker n z * Complex.exp (markerStepLog z n) := by
  have her : Complex.exp (markerStepLog z n) =
      (1 + z / n) * Complex.exp (-z * Complex.log (1 + 1 / (n : ℂ))) := by
    unfold markerStepLog
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hz]
    congr 1
    congr 1
    ring
  have he : Complex.exp (-z * Complex.log ((n : ℂ) + 1)) =
      Complex.exp (-z * Complex.log n) * Complex.exp (-z * Complex.log (1 + 1 / (n : ℂ))) := by
    rw [← Complex.exp_add, log_nat_ratio hn]
    congr 1
    ring
  rw [her]
  unfold normalizedMarker
  rw [Nat.cast_add, Nat.cast_one]
  calc
    Complex.exp (-z * Complex.log ((n : ℂ) + 1)) * ((n : ℂ) + 1) * markerValue (n + 1) z =
        Complex.exp (-z * Complex.log ((n : ℂ) + 1)) * ((z + n) * markerValue n z) := by
          rw [mul_assoc, markerValue_step]
    _ = _ := by
      rw [he]
      field_simp
      ring

#print axioms markerStepExp_bound
#print axioms normalizedMarker_tendsto
#print axioms normalizedMarker_step
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
