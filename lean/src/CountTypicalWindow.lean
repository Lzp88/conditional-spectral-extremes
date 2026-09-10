import ActualNormalizationBounds
import ReservoirShiftUniform

/-! The actual typical reservoir-count window and uniform Gamma ratios. -/
noncomputable section
open Filter Set
open scoped Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale

def TypicalReservoirCount (n : ℕ) (κ : ℝ) (l : ℕ) : Prop :=
  |(l : ℝ)-κ*T n| ≤ (T n)^(3/4 : ℝ)

theorem typical_reservoir_ratio_difference {n l : ℕ} {κ : ℝ}
    (hT : 0 < T n) (ht : TypicalReservoirCount n κ l) :
    |(l : ℝ)/T n-κ| ≤ (T n)^(-(1/4 : ℝ)) := by
  calc
    _ = |(l : ℝ)-κ*T n|/T n := by
      rw [show |(l : ℝ)-κ*T n|/T n = |((l : ℝ)-κ*T n)/T n| by rw [abs_div, abs_of_pos hT]]
      congr 1
      field_simp
    _ ≤ (T n)^(3/4 : ℝ)/T n := div_le_div_of_nonneg_right ht hT.le
    _ = (T n)^(-(1/4 : ℝ)) := by
      rw [show -(1/4 : ℝ) = 3/4-1 by norm_num, Real.rpow_sub hT, Real.rpow_one]

theorem typical_reservoir_error_tendsto_zero :
    Tendsto (fun n => (T n)^(-(1/4 : ℝ))) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp T_tendsto_atTop

theorem eventually_typical_reservoir_window {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop,
      ∀ κ ∈ Icc a B, ∀ l : ℕ, TypicalReservoirCount n κ l →
        (l : ℝ)/T n ∈ Icc (a/2) (2*B) ∧ |(l : ℝ)/T n-κ| < δ := by
  have hB : 0 < B := ha.trans_le haB
  filter_upwards [T_tendsto_atTop.eventually_gt_atTop 0,
    typical_reservoir_error_tendsto_zero.eventually (gt_mem_nhds (show 0 < min δ (min (a/2) B) by positivity))]
      with n hT he κ hκ l ht
  have hh := (typical_reservoir_ratio_difference hT ht).trans_lt he
  have hd := hh.trans_le (min_le_left _ _)
  have hmin := hh.trans_le (min_le_right _ _)
  have hha := abs_lt.mp (hmin.trans_le (min_le_left _ _))
  have hhB := abs_lt.mp (hmin.trans_le (min_le_right _ _))
  exact ⟨⟨by linarith [hκ.1], by linarith [hκ.2]⟩, hd⟩

theorem gamma_ratio_uniform_close {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc a B,
      ∀ y ∈ Icc a B, |x-y| < δ → |Real.Gamma x/Real.Gamma y-1| < ε := by
  obtain ⟨g, G, hg, _, hb⟩ := gamma_two_sided_on_positive_interval ha haB
  have hc : ContinuousOn Real.Gamma (Icc a B) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hc)
    (ε*g) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  have hh : |Real.Gamma x-Real.Gamma y| < ε*g := by
    simpa only [Real.dist_eq] using hd x hx y hy (by simpa only [Real.dist_eq] using hxy)
  have hgy : 0 < Real.Gamma y := Real.Gamma_pos_of_pos (ha.trans_le hy.1)
  have heq : Real.Gamma x/Real.Gamma y-1 = (Real.Gamma x-Real.Gamma y)/Real.Gamma y := by field_simp
  rw [heq, abs_div, abs_of_pos hgy]
  apply (div_lt_iff₀ hgy).mpr
  exact hh.trans_le (mul_le_mul_of_nonneg_left (hb y hy).1 hε.le)

theorem eventually_typical_gamma_ratio {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      ∀ κ ∈ Icc a B, ∀ l : ℕ, TypicalReservoirCount n κ l →
        |Real.Gamma κ/Real.Gamma ((l : ℝ)/T n)-1| < ε := by
  obtain ⟨δ, hδ, hd⟩ := gamma_ratio_uniform_close (a := a/2) (B := 2*B)
    (by positivity) (by linarith) ε hε
  filter_upwards [eventually_typical_reservoir_window ha haB δ hδ] with n hn κ hκ l ht
  obtain ⟨hl, he⟩ := hn κ hκ l ht
  apply hd κ ⟨by linarith [hκ.1], by linarith [hκ.2]⟩ ((l : ℝ)/T n) hl
  simpa only [abs_sub_comm] using he

#print axioms typical_reservoir_ratio_difference
#print axioms typical_reservoir_error_tendsto_zero
#print axioms eventually_typical_reservoir_window
#print axioms gamma_ratio_uniform_close
#print axioms eventually_typical_gamma_ratio

end ConditionalSpectralExtremes.BlockCounts
