import NormalizationUniformBounds

/-! Uniform parameter control after deleting at most two cycles and a bounded fraction of mass. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem normalization_ratio_window {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    {n r k m : ℕ} (hn : 2 ≤ n) (hnr : n ≤ 4 * r) (hrn : r ≤ n) (hm : m ≤ 2)
    (hlog : 2 * Real.log 4 ≤ Real.log n) (hlarge : 4 ≤ a * Real.log n)
    (hka : a ≤ (k : ℝ) / Real.log n) (hkB : (k : ℝ) / Real.log n ≤ B) :
    m ≤ k ∧ 0 < Real.log r ∧
      (1 / 2 : ℝ) * Real.log n ≤ Real.log r ∧ Real.log r ≤ Real.log n ∧
      a / 2 ≤ ((k - m : ℕ) : ℝ) / Real.log r ∧
        ((k - m : ℕ) : ℝ) / Real.log r ≤ 2 * B := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hkn : a * Real.log n ≤ (k : ℝ) := (le_div_iff₀ hLn).1 hka
  have hknB : (k : ℝ) ≤ B * Real.log n := (div_le_iff₀ hLn).1 hkB
  have hk4 : 4 ≤ k := by exact_mod_cast (hlarge.trans hkn)
  have hmk : m ≤ k := by omega
  have hbase := Real.log_le_log hnp (show (n : ℝ) ≤ 4 * r by exact_mod_cast hnr)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hrp.ne'] at hbase
  have hhalf : (1 / 2 : ℝ) * Real.log n ≤ Real.log r := by linarith
  have hLr : 0 < Real.log r := by linarith
  have hLrn : Real.log r ≤ Real.log n := Real.log_le_log hrp (by exact_mod_cast hrn)
  have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have hB : 0 < B := ha.trans_le haB
  refine ⟨hmk, hLr, hhalf, hLrn, ?_, ?_⟩
  · apply (le_div_iff₀ hLr).2
    rw [Nat.cast_sub hmk]
    nlinarith
  · apply (div_le_iff₀ hLr).2
    rw [Nat.cast_sub hmk]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem normalizationBase_ratio {n r k m : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r) (hm : m ≤ k) :
    normalizationBase r (k - m) / normalizationBase n k =
      ((n : ℝ) / r) * ((k.descFactorial m : ℝ) / (Real.log n) ^ m) *
        (Real.log r / Real.log n) ^ (k - m) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hLr : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hf : ((k - m).factorial : ℝ) ≠ 0 := by exact_mod_cast (k - m).factorial_ne_zero
  have hfac : (k.factorial : ℝ) = (k - m).factorial * (k.descFactorial m : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hm).symm
  have hpow : (Real.log n) ^ k = (Real.log n) ^ (k - m) * (Real.log n) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  unfold normalizationBase
  rw [hfac, hpow, div_pow]
  field_simp

#print axioms normalization_ratio_window
#print axioms normalizationBase_ratio
end ConditionalSpectralExtremes
