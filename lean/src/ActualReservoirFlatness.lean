import ReservoirLeadingFlatness

/-! Equation (flatness) for the actual bivariate reservoir coefficients.
All analytic errors and all scale comparisons are proved in the imports. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale Reservoir

theorem actual_reservoir_flatness_time_bound {a B C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
        ∀ l : ℕ, a ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ B →
        0 < reservoirCoefficient n (cutoff n) n l ∧
        |reservoirCoefficient (n-d) (cutoff n) (n-d) l /
            reservoirCoefficient n (cutoff n) n l - 1| ≤ C/T n + D/(L n)^3 := by
  obtain ⟨C, D, hC, hD, herr⟩ := actual_reservoir_error_fixed_window ha haB hC₀
  obtain ⟨R, hR, hlead⟩ := actual_reservoir_leading_flatness (B := B) ha hC₀
  have hη := (reservoir_error_envelope_tendsto_zero C D).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hρ := (reservoir_error_envelope_tendsto_zero 0 R).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨6*C, 6*D+2*R, by positivity, by positivity, ?_⟩
  filter_upwards [herr, hlead, hη, hρ, eventually_reservoir_shift_scales hC₀,
    eventually_shift_ge hC₀ 1, eventually_ge_atTop 1,
    T_tendsto_atTop.eventually_gt_atTop 0, L_tendsto_atTop.eventually_gt_atTop 0]
      with n he hl hnη hnρ hs hN hn ht hL d hd l hal hlB
  have hd0 : (0 : ℝ) ≤ C₀ * L n * cutoff n := by positivity
  have he0 := he 0 (by simpa using hd0) l hal hlB
  simp only [Nat.sub_zero] at he0
  have hed := he d hd l hal hlB
  have hld := hl d hd l hal hlB
  have hlp : 0 < l := by
    have : 0 < (l : ℝ) := (div_pos_iff_of_pos_right ht).mp (ha.trans_le hal)
    exact_mod_cast this
  have hshift := hs d hd
  have hp := reservoirLeading_pos (hN d hd) hshift.2.2.1 hlp
  have hq := reservoirLeading_pos (show 0 < n from hn) ht hlp
  have hρ1 : R/(L n)^3 ≤ 1 := by simpa only [zero_div, zero_add] using hnρ.le
  have hh := relative_ratio_error hp hq (by positivity : 0 ≤ C/T n+D/(L n)^3)
    hnη.le (by positivity : 0 ≤ R/(L n)^3) hρ1 hed he0 hld
  refine ⟨hh.1, ?_⟩
  convert! hh.2 using 1
  ring

theorem actual_reservoir_flatness {a B C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
        ∀ l : ℕ, a ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ B →
        0 < reservoirCoefficient n (cutoff n) n l ∧
        |reservoirCoefficient n (cutoff n) (n-d) l /
            reservoirCoefficient n (cutoff n) n l - 1| ≤
          C * ((ell n)⁻¹ + (L n)^(-3 : ℤ)) := by
  obtain ⟨C, D, hC, hD, he⟩ := actual_reservoir_flatness_time_bound ha haB hC₀
  have hratio := reservoir_scale_ratio_tendsto_four.eventually
    (lt_mem_nhds (by norm_num : (1 : ℝ) < 4))
  refine ⟨C+D, by positivity, ?_⟩
  filter_upwards [he, hratio, ell_tendsto_atTop.eventually_gt_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0, eventually_reservoir_shift_scales hC₀]
      with n hn hT heℓ hL hs d hd l hal hlB
  obtain ⟨hpos, hbound⟩ := hn d hd l hal hlB
  have hET : ell n ≤ T n := by
    have := (lt_div_iff₀ heℓ).mp hT
    linarith
  have hTp : 0 < T n := heℓ.trans_le hET
  obtain ⟨hb, hNb, _, _, _, _, _⟩ := hs d hd
  have hbN : cutoff n ≤ n-d := by omega
  have hbn : cutoff n ≤ n := hbN.trans (Nat.sub_le n d)
  have hambient := reservoirCoefficient_ambient_invariant (n-d) n (cutoff n) (n-d) l
    hbN le_rfl hbn (Nat.sub_le n d)
  rw [hambient] at hbound
  refine ⟨hpos, hbound.trans ?_⟩
  calc
    _ ≤ C/ell n + D/(L n)^3 := add_le_add
      (div_le_div_of_nonneg_left hC.le heℓ hET) le_rfl
    _ ≤ (C+D)/ell n + (C+D)/(L n)^3 := by gcongr <;> linarith
    _ = _ := by simp only [zpow_neg, zpow_ofNat]; ring

theorem reservoir_flatness_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n => C*((ell n)⁻¹+(L n)^(-3 : ℤ))) atTop (𝓝 0) := by
  have hL3 : Tendsto (fun n => (L n)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp L_tendsto_atTop
  have he := ell_tendsto_atTop.inv_tendsto_atTop.add hL3.inv_tendsto_atTop
  simpa only [zero_add, mul_zero, zpow_neg, zpow_ofNat, Pi.inv_apply] using! he.const_mul C

#print axioms actual_reservoir_flatness
#print axioms reservoir_flatness_error_tendsto_zero
end ConditionalSpectralExtremes.ReservoirAnalysis
