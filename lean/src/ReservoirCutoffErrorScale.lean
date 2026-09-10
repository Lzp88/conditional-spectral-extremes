import ActualReservoirCutoff

/-! Uniform relative error with the fixed, unshifted marker window l/T. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale Reservoir

theorem reservoir_sqrt_error_scale {n N : ℕ} (hn : 2 ≤ n)
    (hN : n ≤ 2*N) (hL : 1 ≤ L n)
    (hT : reservoirTime (cutoff n) N ≤ L n) :
    Real.sqrt (reservoirTime (cutoff n) N) * cutoff n / N ≤ 2 / (L n)^3 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNr : (n : ℝ) ≤ 2*N := by exact_mod_cast hN
  have hLp : 0 < L n := by linarith
  have hs : Real.sqrt (reservoirTime (cutoff n) N) ≤ L n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith
  have hb : (cutoff n : ℝ) ≤ (n : ℝ)/(L n)^4 := cutoff_le_unrounded n
  calc
    _ ≤ L n * cutoff n / N := by gcongr
    _ ≤ L n * ((n : ℝ)/(L n)^4) / N := by gcongr
    _ ≤ 2/(L n)^3 := by
      apply (div_le_iff₀ hNp).2
      field_simp
      nlinarith

theorem actual_reservoir_error_fixed_window {a B C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
        ∀ l : ℕ, a ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ B →
        |reservoirCoefficient (n-d) (cutoff n) (n-d) l /
            reservoirLeading (cutoff n) (n-d) l - 1| ≤ C/T n + D/(L n)^3 := by
  have hB : 0 < B := ha.trans_le haB
  obtain ⟨C, D, hC, hD, he⟩ := actual_reservoir_marker_at_cutoff ha
    (show a ≤ 2*B by linarith) hC₀
  refine ⟨2*C, 2*D, by positivity, by positivity, ?_⟩
  filter_upwards [he, eventually_reservoir_shift_scales hC₀,
    eventually_short_mass_half hC₀, eventually_ge_atTop 2,
    T_tendsto_atTop.eventually_gt_atTop 0, L_tendsto_atTop.eventually_ge_atTop 1]
      with n hn hs hh hn2 ht hL d hd l hal hlB
  obtain ⟨_, _, hx, hhalf, hxt, _, hTL⟩ := hs d hd
  have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
  have hla : a ≤ (l : ℝ)/reservoirTime (cutoff n) (n-d) :=
    hal.trans (div_le_div_of_nonneg_left hl0 hx hxt)
  have hlb : (l : ℝ)/reservoirTime (cutoff n) (n-d) ≤ 2*B := by
    apply (div_le_iff₀ hx).2
    have := (div_le_iff₀ ht).mp hlB
    nlinarith
  have he' := hn d hd l hla hlb
  have hfirst : C/reservoirTime (cutoff n) (n-d) ≤ 2*C/T n := by
    apply (div_le_div_iff₀ hx ht).2
    nlinarith
  have hsecond := mul_le_mul_of_nonneg_left
    (reservoir_sqrt_error_scale hn2 (by have := hh d hd; omega) hL hTL) hD.le
  calc
    _ ≤ C/reservoirTime (cutoff n) (n-d) +
        D*Real.sqrt (reservoirTime (cutoff n) (n-d))*cutoff n/(n-d : ℕ) := he'
    _ ≤ 2*C/T n + 2*D/(L n)^3 := by
      convert! add_le_add hfirst hsecond using 1 <;> ring

theorem reservoir_error_envelope_tendsto_zero (C D : ℝ) :
    Tendsto (fun n => C/T n + D/(L n)^3) atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds (x := C)).div_atTop T_tendsto_atTop
  have hL3 : Tendsto (fun n => (L n)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp L_tendsto_atTop
  simpa using ht.add ((tendsto_const_nhds (x := D)).div_atTop hL3)

#print axioms actual_reservoir_error_fixed_window
end ConditionalSpectralExtremes.ReservoirAnalysis
