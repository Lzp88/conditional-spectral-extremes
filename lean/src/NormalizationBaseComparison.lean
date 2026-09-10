import NormalizationRatioWindow

/-! Uniform bound for the explicit leading coefficient after at most two cycle deletions. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem normalizationBase_ratio_le {B : ℝ} {n r k m : ℕ}
    (hn : 2 ≤ n) (hr : 2 ≤ r) (hnr : n ≤ 4 * r) (hrn : r ≤ n)
    (hm : m ≤ 2) (hmk : m ≤ k) (hkB : (k : ℝ) / Real.log n ≤ B) :
    normalizationBase r (k - m) / normalizationBase n k ≤ 4 * (max 1 B) ^ 2 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hLr : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hsize : (n : ℝ) / r ≤ 4 := (div_le_iff₀ hrp).2 (by exact_mod_cast hnr)
  have hlog : Real.log r / Real.log n ≤ 1 :=
    (div_le_one hLn).2 (Real.log_le_log hrp (by exact_mod_cast hrn))
  have hlogpow : (Real.log r / Real.log n) ^ (k - m) ≤ 1 := pow_le_one₀ (by positivity) hlog
  have hdesc : (k.descFactorial m : ℝ) / (Real.log n) ^ m ≤ (max 1 B) ^ 2 := by
    calc
      _ ≤ (k : ℝ) ^ m / (Real.log n) ^ m :=
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow k m) (by positivity)
      _ = ((k : ℝ) / Real.log n) ^ m := (div_pow _ _ _).symm
      _ ≤ (max 1 B) ^ m := pow_le_pow_left₀ (by positivity) (hkB.trans (le_max_right _ _)) m
      _ ≤ (max 1 B) ^ 2 := pow_le_pow_right₀ (le_max_left _ _) hm
  rw [normalizationBase_ratio hn hr hmk]
  calc
    _ ≤ ((n : ℝ) / r) * ((k.descFactorial m : ℝ) / (Real.log n) ^ m) * 1 :=
      mul_le_mul_of_nonneg_left hlogpow (by positivity)
    _ ≤ 4 * (max 1 B) ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hsize hdesc (by positivity) (by norm_num)
    _ = _ := by ring

#print axioms normalizationBase_ratio_le
end ConditionalSpectralExtremes
