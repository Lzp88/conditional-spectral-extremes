import NormalizationBaseComparison

/-! The actual uniform coefficient ratio used by the conditional cross-mass argument. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem actual_coefficient_ratio_bounded {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ (r k m : ℕ),
      n ≤ 4 * r → r ≤ n → m ≤ 2 →
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      0 < coefficient n k ∧ coefficient r (k - m) / coefficient n k ≤ D := by
  have hB : 0 < B := ha.trans_le haB
  obtain ⟨c, C, hc, hC, N, hN, hb⟩ :=
    actual_normalization_uniform_bounds (a := a / 2) (B := 2 * B) (by positivity) (by linarith)
  have hLtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL, hNL⟩ := eventually_atTop.1
    (hLtop.eventually_ge_atTop (max (2 * Real.log 4) (4 / a)))
  refine ⟨(C / c) * (4 * (max 1 B) ^ 2), by positivity, max (4 * N) NL, ?_, ?_⟩
  · omega
  intro n hn r k m hnr hrn hm hak hkB
  have hn4N : 4 * N ≤ n := (le_max_left (4 * N) NL).trans hn
  have hnN : N ≤ n := by omega
  have hrN : N ≤ r := by omega
  have hn2 : 2 ≤ n := by omega
  have hr2 : 2 ≤ r := by omega
  have hLs := hNL n ((le_max_right (4 * N) NL).trans hn)
  have hlog : 2 * Real.log 4 ≤ Real.log n := (le_max_left _ _).trans hLs
  have hlarge : 4 ≤ a * Real.log n := by
    have he := (div_le_iff₀ ha).1 ((le_max_right _ _).trans hLs)
    nlinarith
  obtain ⟨hmk, _, _, _, hralo, hrahi⟩ := normalization_ratio_window ha haB hn2 hnr hrn hm
    hlog hlarge hak hkB
  obtain ⟨hden, _⟩ := hb n hnN k (by linarith) (by linarith)
  obtain ⟨_, hnum⟩ := hb r hrN (k - m) hralo hrahi
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hLr : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hbaseN : 0 < normalizationBase n k := by unfold normalizationBase; positivity
  have hbaseR : 0 ≤ normalizationBase r (k - m) := by unfold normalizationBase; positivity
  have hdenPos : 0 < coefficient n k := (mul_pos hc hbaseN).trans_le hden
  refine ⟨hdenPos, ?_⟩
  calc
    _ ≤ (C * normalizationBase r (k - m)) / coefficient n k :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (C * normalizationBase r (k - m)) / (c * normalizationBase n k) :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le hbaseR) (mul_pos hc hbaseN) hden
    _ = (C / c) * (normalizationBase r (k - m) / normalizationBase n k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalizationBase_ratio_le hn2 hr2 hnr hrn hm hmk hkB)
      (by positivity)

#print axioms actual_coefficient_ratio_bounded
end ConditionalSpectralExtremes
