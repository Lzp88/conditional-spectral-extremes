import ReservoirOuterDecayAlgebra
import ReservoirShiftUniform

/-! Actual outer-contour error is negligible uniformly over the manuscript's size shifts. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale

theorem eventually_outer_decay_envelope {M C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
      ((n - d : ℕ) : ℝ) * reservoirOuterError M (cutoff n) (n - d) * (L n) ^ q ≤
        (2 * Real.pi * reservoirOuterConstant M) / n := by
  filter_upwards [eventually_short_mass_half hC₀, eventually_four_cutoff_le_n,
    cutoff_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop 2,
    L_tendsto_atTop.eventually_ge_atTop 1,
    L_tendsto_atTop.eventually_ge_atTop (4 * (reservoirOuterPower M + q + 2))]
      with n hh hb hb0 hn hL hlarge d hd
  have hhalf := hh d hd
  simpa only [L] using reservoir_outer_decay_bound hM hn (by omega : 0 < cutoff n)
    (by omega : cutoff n ≤ n) (Nat.sub_le n d) (by omega : n ≤ 2 * (n - d))
    (cutoff_le_unrounded n) q hL hlarge

theorem uniform_outer_error_negligible {M C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n ≥ N₀, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
      ((n - d : ℕ) : ℝ) * reservoirOuterError M (cutoff n) (n - d) * (L n) ^ q < ε := by
  have hsmall := ((tendsto_const_nhds (x := 2 * Real.pi * reservoirOuterConstant M)).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (gt_mem_nhds hε)
  have he : ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
      ((n - d : ℕ) : ℝ) * reservoirOuterError M (cutoff n) (n - d) * (L n) ^ q < ε := by
    filter_upwards [eventually_outer_decay_envelope hM hC₀ q, hsmall] with n hn hs d hd
    exact (hn d hd).trans_lt hs
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 he
  exact ⟨max N₀ 2, le_max_right _ _, fun n hn => hN₀ n ((le_max_left _ _).trans hn)⟩

theorem eventually_outer_error_over_time {M C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
      ((n - d : ℕ) : ℝ) * reservoirOuterError M (cutoff n) (n - d) ≤
        (2 * Real.pi * reservoirOuterConstant M) / reservoirTime (cutoff n) (n - d) := by
  filter_upwards [eventually_outer_decay_envelope hM hC₀ 1,
    eventually_reservoir_shift_scales hC₀, eventually_ge_atTop 2] with n he hs hn d hd
  obtain ⟨_, _, hT, _, _, _, hTL⟩ := hs d hd
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hK : 0 ≤ 2 * Real.pi * reservoirOuterConstant M := by
    have := reservoirOuterConstant_pos M
    positivity
  apply (le_div_iff₀ hT).2
  calc
    _ ≤ ((n - d : ℕ) : ℝ) * reservoirOuterError M (cutoff n) (n - d) * L n :=
      mul_le_mul_of_nonneg_left hTL (mul_nonneg (Nat.cast_nonneg _)
        (reservoirOuterError_nonneg _ _ _))
    _ ≤ (2 * Real.pi * reservoirOuterConstant M) / n := by simpa only [pow_one] using he d hd
    _ ≤ _ := div_le_self hK hnp

#print axioms uniform_outer_error_negligible
#print axioms eventually_outer_error_over_time
end ConditionalSpectralExtremes.ReservoirAnalysis
