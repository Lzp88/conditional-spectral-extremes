import ReservoirLeadingComparison
import RelativeRatioAlgebra
import ReservoirCutoffErrorScale

/-! The explicit saddle main term is uniformly flat under the actual size shifts. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale

theorem actual_reservoir_leading_flatness {a B C₀ : ℝ}
    (ha : 0 < a) (hC₀ : 0 ≤ C₀) :
    ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
        ∀ l : ℕ, a ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ B →
        |reservoirLeading (cutoff n) (n-d) l / reservoirLeading (cutoff n) n l - 1| ≤
          R/(L n)^3 := by
  obtain ⟨K, hK, hk⟩ := reservoirLeading_log_ratio_bound (B := B) ha
  let R := 4*K*(C₀+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hL3 : Tendsto (fun n => (L n)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp L_tendsto_atTop
  have hsmall := ((tendsto_const_nhds (x := R)).div_atTop hL3).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨R, hR, ?_⟩
  filter_upwards [eventually_reservoir_shift_scales hC₀, T_tendsto_atTop.eventually_ge_atTop 1,
    eventually_shift_ge hC₀ 1, eventually_ge_atTop 1,
    L_tendsto_atTop.eventually_gt_atTop 0, hsmall]
      with n hs ht hN hn hL hsmalln d hd l hal hlB
  obtain ⟨_, _, hx, hhalf, hxt, hdiff, _⟩ := hs d hd
  have htp : 0 < T n := by linarith
  have hl : 0 < l := by
    have : 0 < (l : ℝ) := (div_pos_iff_of_pos_right htp).mp (ha.trans_le hal)
    exact_mod_cast this
  have hNp : 0 < n-d := hN d hd
  have hnp : 0 < n := hn
  have htn : reservoirTime (cutoff n) n = T n := rfl
  have hlog := hk (cutoff n) (n-d) n l hNp hnp hl ht hhalf hxt hal hlB
  have hlog' : |Real.log (reservoirLeading (cutoff n) (n-d) l /
      reservoirLeading (cutoff n) n l)| ≤ K*(2*C₀/(L n)^3) :=
    hlog.trans (mul_le_mul_of_nonneg_left hdiff hK.le)
  have hδ : 0 ≤ 2*C₀/(L n)^3 := by positivity
  have hKR : K*(2*C₀/(L n)^3) ≤ R/(L n)^3 := by
    dsimp [R]
    have hh : 2*K*C₀ ≤ 4*K*(C₀+1) := by nlinarith
    convert! div_le_div_of_nonneg_right hh (pow_nonneg hL.le 3) using 1
    ring
  have he := positive_ratio_error_of_log (reservoirLeading_pos hNp hx hl)
    (reservoirLeading_pos hnp htp hl) hK.le hδ (hKR.trans hsmalln.le) hlog'
  calc
    _ ≤ 2*K*(2*C₀/(L n)^3) := he
    _ ≤ R/(L n)^3 := by
      dsimp [R]
      have hh : 4*K*C₀ ≤ 4*K*(C₀+1) := by nlinarith
      convert! div_le_div_of_nonneg_right hh (pow_nonneg hL.le 3) using 1
      ring

#print axioms actual_reservoir_leading_flatness
end ConditionalSpectralExtremes.ReservoirAnalysis
