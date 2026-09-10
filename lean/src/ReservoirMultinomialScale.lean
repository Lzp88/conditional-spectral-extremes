import CountTypicalWindow
import ActualReservoirFlatness

/-! The exact reservoir-to-multinomial scalar and its actual analytic errors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

def reservoirMultinomialScale (n k l : ℕ) : ℝ :=
  reservoirCoefficient n (cutoff n) n l / coefficient n k *
    ((L n)^k * (l.factorial : ℝ) / ((T n)^l * (k.factorial : ℝ)))

theorem reservoir_multinomial_scale_error {n k l : ℕ} {η ρ : ℝ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hl : 1 ≤ l) (hT : 0 < T n)
    (hη : 0 ≤ η) (hηh : η ≤ 1/2) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hR : |reservoirCoefficient n (cutoff n) n l / reservoirLeading (cutoff n) n l-1| ≤ η)
    (hA : |coefficient n k/normalizationLeading n k-1| ≤ η)
    (hG : |Real.Gamma ((k : ℝ)/L n)/Real.Gamma ((l : ℝ)/T n)-1| ≤ ρ) :
    |reservoirMultinomialScale n k l-1| ≤ 6*η+2*ρ := by
  have hL : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hn0 : 0 < n := by omega
  have hl0 : 0 < l := by omega
  have hRL := reservoirLeading_pos (b := cutoff n) hn0 hT hl0
  have hAL := normalizationLeading_pos hn hk
  let S : ℝ := (L n)^k * (l.factorial : ℝ) / ((T n)^l * (k.factorial : ℝ))
  have hS : 0 < S := by dsimp [S]; positivity
  have hrr : |(reservoirCoefficient n (cutoff n) n l*S)/(reservoirLeading (cutoff n) n l*S)-1| ≤ η := by
    simpa only [mul_div_mul_right _ _ hS.ne'] using hR
  have heq : (reservoirLeading (cutoff n) n l*S)/normalizationLeading n k =
      Real.Gamma ((k : ℝ)/L n)/Real.Gamma ((l : ℝ)/T n) := by
    have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
    have hlp : 0 < (l : ℝ) := by exact_mod_cast hl
    have hGk := Real.Gamma_pos_of_pos (div_pos hkp hL)
    have hGl := Real.Gamma_pos_of_pos (div_pos hlp hT)
    unfold reservoirLeading normalizationLeading S reservoirTime
    change ((T n)^l / ((n : ℝ)*l.factorial*Real.Gamma ((l : ℝ)/T n)) *
      ((L n)^k*l.factorial/((T n)^l*k.factorial))) /
      ((L n)^k/((n : ℝ)*k.factorial*Real.Gamma ((k : ℝ)/L n))) = _
    field_simp
  have hh := relative_ratio_error (mul_pos hRL hS) hAL hη hηh hρ hρ1 hrr hA (by rw [heq]; exact hG)
  have hnorm : (reservoirCoefficient n (cutoff n) n l*S)/coefficient n k =
      reservoirMultinomialScale n k l := by
    unfold reservoirMultinomialScale S
    ring
  rw [hnorm] at hh
  exact hh.2

/-- Actual reservoir/normalization scalar tends to one on the manuscript's
typical long-count window, uniformly in k/log n on a fixed positive compact. -/
theorem actual_reservoir_multinomial_scale_tendsto {a B : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ l : ℕ, TypicalReservoirCount n ((k : ℝ)/L n) l →
        |reservoirMultinomialScale n k l-1| < ε := by
  have hB : 0 < B := ha.trans_le haB
  obtain ⟨C, D, hC, hD, hR⟩ := actual_reservoir_error_fixed_window
    (a := a/2) (B := 2*B) (C₀ := 0) (by positivity) (by linarith) le_rfl
  obtain ⟨A, hA, N, hN, hAb⟩ := actual_normalization_relative_error ha haB
  let η : ℕ → ℝ := fun n => C/T n+D/(L n)^3+A/L n
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa only [add_zero] using (reservoir_error_envelope_tendsto_zero C D).add
      ((tendsto_const_nhds (x := A)).div_atTop L_tendsto_atTop)
  let ρ : ℝ := min (ε/8) (1/2)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hηsmall := hη.eventually (gt_mem_nhds (show (0 : ℝ) < min (ε/12) (1/2) by positivity))
  filter_upwards [hR, eventually_ge_atTop N, T_tendsto_atTop.eventually_gt_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0, hηsmall,
    eventually_typical_reservoir_window ha haB 1 (by norm_num),
    eventually_typical_gamma_ratio ha haB ρ hρ] with n hr hn hT hL hηs hwindow hgamma
  intro k hak hkB l htyp
  have hlwindow := (hwindow ((k : ℝ)/L n) ⟨hak, hkB⟩ l htyp).1
  have hk : 1 ≤ k := by
    have hh : 0 < (k : ℝ) := (div_pos_iff_of_pos_right hL).mp (ha.trans_le hak)
    have : 0 < k := by exact_mod_cast hh
    omega
  have hl : 1 ≤ l := by
    have hh : 0 < (l : ℝ) := (div_pos_iff_of_pos_right hT).mp
      ((by positivity : (0 : ℝ) < a/2).trans_le hlwindow.1)
    have : 0 < l := by exact_mod_cast hh
    omega
  have hRe := hr 0 (by simp) l hlwindow.1 hlwindow.2
  simp only [Nat.sub_zero] at hRe
  have hAe := hAb n hn k hk hak hkB
  have hAn : 0 ≤ A/L n := by positivity
  have hRn : 0 ≤ C/T n+D/(L n)^3 := by positivity
  have hh := reservoir_multinomial_scale_error (hN.trans hn) hk hl hT
    (show 0 ≤ η n by dsimp [η]; positivity)
    (hηs.le.trans (min_le_right _ _)) hρ.le
    (show ρ ≤ 1 by dsimp [ρ]; have := min_le_right (ε/8) (1/2 : ℝ); linarith)
    (hRe.trans (by dsimp [η]; linarith))
    (show |coefficient n k/normalizationLeading n k-1| ≤ η n from
      hAe.trans (by change A/L n ≤ η n; dsimp only [η]; linarith))
    (hgamma ((k : ℝ)/L n) ⟨hak, hkB⟩ l htyp).le
  have he := hηs.trans_le (min_le_left _ _)
  have hρe : ρ ≤ ε/8 := min_le_left _ _
  linarith

#print axioms reservoir_multinomial_scale_error
#print axioms actual_reservoir_multinomial_scale_tendsto

end ConditionalSpectralExtremes.BlockCounts
