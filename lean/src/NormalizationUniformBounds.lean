import ActualNormalizationBounds

/-! Uniform Gamma-free bounds for actual normalization coefficients. -/
noncomputable section
open Set
namespace ConditionalSpectralExtremes

def normalizationBase (n k : ℕ) : ℝ := (Real.log n) ^ k / ((n : ℝ) * k.factorial)

theorem normalizationLeading_eq_base (n k : ℕ) :
    normalizationLeading n k = normalizationBase n k / Real.Gamma ((k : ℝ) / Real.log n) := by
  unfold normalizationLeading normalizationBase
  ring

theorem actual_normalization_uniform_bounds {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : ℕ,
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      c * normalizationBase n k ≤ coefficient n k ∧
        coefficient n k ≤ C * normalizationBase n k := by
  obtain ⟨g, G, hg, hG, hb⟩ := gamma_two_sided_on_positive_interval ha haB
  obtain ⟨N, hN, hfact⟩ := actual_normalization_factor_bounds ha haB
  refine ⟨1 / (2 * G), 2 / g, by positivity, by positivity, N, hN, ?_⟩
  intro n hn k hak hkB
  have hn2 : 2 ≤ n := hN.trans hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hbase : 0 ≤ normalizationBase n k := by unfold normalizationBase; positivity
  have hγ := Real.Gamma_pos_of_pos (ha.trans_le hak)
  obtain ⟨hγlo, hγhi⟩ := hb _ ⟨hak, hkB⟩
  obtain ⟨hlo, hhi⟩ := hfact n hn k hak hkB
  rw [normalizationLeading_eq_base] at hlo hhi
  constructor
  · calc
      _ = (1 / 2 : ℝ) * (normalizationBase n k / G) := by ring
      _ ≤ (1 / 2 : ℝ) * (normalizationBase n k / Real.Gamma ((k : ℝ) / Real.log n)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hbase hγ hγhi) (by norm_num)
      _ ≤ _ := hlo
  · calc
      _ ≤ (3 / 2 : ℝ) * (normalizationBase n k / Real.Gamma ((k : ℝ) / Real.log n)) := hhi
      _ ≤ (3 / 2 : ℝ) * (normalizationBase n k / g) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hbase hg hγlo) (by norm_num)
      _ ≤ 2 * (normalizationBase n k / g) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring

#print axioms actual_normalization_uniform_bounds
end ConditionalSpectralExtremes
