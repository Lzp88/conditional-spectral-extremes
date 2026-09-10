import ActualMarkerAsymptotic

/-! The manuscript's real relative asymptotic for the actual normalization a_(n,k). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

theorem actual_normalization_absolute_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : ℕ, 1 ≤ k →
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      |((n : ℝ) * k.factorial / (Real.log n) ^ k) * coefficient n k -
        (Real.Gamma ((k : ℝ) / Real.log n))⁻¹| ≤ C / Real.log n := by
  obtain ⟨C, hC, N, hN, he⟩ := actual_marker_normalized_error ha haB
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn k hk hak hkB
  have hb := he n hn k hk hak hkB
  have hc : ‖(((n : ℝ) * k.factorial / (Real.log n) ^ k) * coefficient n k -
      (Real.Gamma ((k : ℝ) / Real.log n))⁻¹ : ℝ)‖ ≤ C / Real.log n := by
    simpa only [Complex.Gamma_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real] using hb
  simpa only [Real.norm_eq_abs] using hc

theorem gamma_bounded_on_positive_interval {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ G : ℝ, 0 < G ∧ ∀ s ∈ Icc a B, Real.Gamma s ≤ G := by
  have hc : ContinuousOn Real.Gamma (Icc a B) := by
    intro s hs
    exact (Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hsp : 0 < s := ha.trans_le hs.1
      linarith)).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 haB) hc
  exact ⟨Real.Gamma s, Real.Gamma_pos_of_pos (ha.trans_le hs.1), fun t ht => hmax ht⟩

theorem actual_normalization_relative_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : ℕ, 1 ≤ k →
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      |coefficient n k /
        ((Real.log n) ^ k / ((n : ℝ) * k.factorial * Real.Gamma ((k : ℝ) / Real.log n))) - 1|
        ≤ C / Real.log n := by
  obtain ⟨C, hC, N, hN, he⟩ := actual_normalization_absolute_error ha haB
  obtain ⟨G, hG, hbound⟩ := gamma_bounded_on_positive_interval ha haB
  refine ⟨C * G, by positivity, N, hN, ?_⟩
  intro n hn k hk hak hkB
  have hn2 : 2 ≤ n := hN.trans hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hGp := Real.Gamma_pos_of_pos (ha.trans_le hak)
  have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have heq : coefficient n k /
      ((Real.log n) ^ k / ((n : ℝ) * k.factorial * Real.Gamma ((k : ℝ) / Real.log n))) - 1 =
      (((n : ℝ) * k.factorial / (Real.log n) ^ k) * coefficient n k -
        (Real.Gamma ((k : ℝ) / Real.log n))⁻¹) * Real.Gamma ((k : ℝ) / Real.log n) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hGp]
  calc
    _ ≤ (C / Real.log n) * Real.Gamma ((k : ℝ) / Real.log n) :=
      mul_le_mul_of_nonneg_right (he n hn k hk hak hkB) hGp.le
    _ ≤ (C / Real.log n) * G := mul_le_mul_of_nonneg_left (hbound _ ⟨hak, hkB⟩) (by positivity)
    _ = (C * G) / Real.log n := by ring

#print axioms actual_normalization_absolute_error
#print axioms actual_normalization_relative_error
end ConditionalSpectralExtremes
