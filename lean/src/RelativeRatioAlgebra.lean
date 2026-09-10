import ActualReservoirCutoff

/-! Explicit, quantitative propagation of relative errors through a ratio. -/
noncomputable section
namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem relative_ratio_error {r s p q η ρ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hη : 0 ≤ η) (hηh : η ≤ 1/2)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hr : |r/p-1| ≤ η) (hs : |s/q-1| ≤ η) (hpq : |p/q-1| ≤ ρ) :
    0 < s ∧ |r/s-1| ≤ 6*η+2*ρ := by
  have hslo : 1-η ≤ s/q := by linarith [(abs_le.mp hs).1]
  have hsy : 0 < s/q := by linarith
  have hsp : 0 < s := (div_pos_iff_of_pos_right hq).mp hsy
  refine ⟨hsp, ?_⟩
  have hpqa : |p/q| ≤ 2 := by
    rw [abs_of_pos (div_pos hp hq)]
    linarith [(abs_le.mp hpq).2]
  have he : (p/q)*(r/p)-s/q = (p/q)*(r/p-1)+(p/q-1)-(s/q-1) := by ring
  have hnum : |(p/q)*(r/p)-s/q| ≤ 3*η+ρ := by
    rw [he]
    calc
      _ ≤ |(p/q)*(r/p-1)+(p/q-1)| + |s/q-1| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ((p/q)*(r/p-1)+(p/q-1)) 0 (s/q-1)
      _ ≤ |(p/q)*(r/p-1)|+|p/q-1|+|s/q-1| := by gcongr; exact abs_add_le _ _
      _ = |p/q| * |r/p-1| + |p/q-1| + |s/q-1| := by rw [abs_mul]
      _ ≤ 2*η+ρ+η := by gcongr
      _ = _ := by ring
  have hratio : r/s-1 = ((p/q)*(r/p)-s/q)/(s/q) := by field_simp
  rw [hratio, abs_div, abs_of_pos hsy]
  apply (div_le_iff₀ hsy).2
  have hn : 0 ≤ 6*η+2*ρ := by positivity
  nlinarith

theorem positive_ratio_error_of_log {p q K δ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (_hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (hsmall : K*δ ≤ 1) (hlog : |Real.log (p/q)| ≤ K*δ) :
    |p/q-1| ≤ 2*K*δ := by
  have he := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log (div_pos hp hq)] at he
  nlinarith

#print axioms relative_ratio_error
end ConditionalSpectralExtremes.ReservoirAnalysis
