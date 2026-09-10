import PathMomentScales
import BridgePathAlgebra

/-! The mixed prefix/suffix normalizer, with every fine-block error
accumulated and the actual prefix counts retained. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem truncated_fine_count_sum (m k : ℕ) (hkm : k ≤ m) (q : ℕ → ℕ) :
    (∑ i : Fin m, if i.val < k then (q (i.val+1) : ℝ) else 0) =
      (FineScales.countPrefix q k : ℝ) := by
  have hh := partialSum_eq_sum_fin m k hkm (fun i : Fin m => (q (i.val+1) : ℝ))
  simp only [FiniteWalk.partialSum, FiniteWalk.prefixIndices, Finset.sum_filter] at hh
  rw [hh]
  simp only [FineScales.countPrefix, Nat.cast_sum]
  exact Fin.sum_univ_eq_sum_range (fun i => (q (i+1) : ℝ)) k

theorem mixed_count_exponent (m k : ℕ) (hkm : k ≤ m) (q : ℕ → ℕ) (lam : ℝ) :
    (∑ i : Fin m, if i.val < k then lam*(q (i.val+1) : ℝ) else lam*(2*(q (i.val+1) : ℝ))) =
      lam*(2*(FineScales.countPrefix q m : ℝ)-(FineScales.countPrefix q k : ℝ)) := by
  have he (i : Fin m) :
      (if i.val < k then lam*(q (i.val+1) : ℝ) else lam*(2*(q (i.val+1) : ℝ))) =
        (2*lam)*(q (i.val+1) : ℝ)-lam*(if i.val < k then (q (i.val+1) : ℝ) else 0) := by
    by_cases hi : i.val < k <;> simp only [hi, ↓reduceIte] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    truncated_fine_count_sum m k hkm q, ← Nat.cast_sum, ← countPrefix_eq_fine_sum]
  ring

theorem positive_normalizer_power_bound (s ε b : ℝ) (hs : -1 < s) (q : ℕ)
    (he : |b/logSineA s^q-1| ≤ ε) :
    b ≤ Real.exp (ε+lambda s*(q : ℝ)) := by
  have hA : 0 < logSineA s^q := pow_pos (logSineA_pos s hs) q
  have hb : b/logSineA s^q ≤ Real.exp ε := by
    have hh := (abs_le.mp he).2
    linarith [Real.add_one_le_exp ε]
  have h := (div_le_iff₀ hA).mp hb
  rw [logSineA_eq_exp_lambda s hs, ← Real.exp_nat_mul, ← Real.exp_add] at h
  simpa only [mul_comm] using h

theorem mixed_normalizer_product_bound (m k : ℕ) (hkm : k ≤ m) (q : ℕ → ℕ)
    (s ε : ℝ) (hs : -1 < s) (b₁ b₂ : Fin m → ℝ)
    (hb₁ : ∀ i, 0 ≤ b₁ i) (hb₂ : ∀ i, 0 ≤ b₂ i)
    (he₁ : ∀ i : Fin m, i.val < k → |b₁ i/logSineA s^q (i.val+1)-1| ≤ ε)
    (he₂ : ∀ i : Fin m, k ≤ i.val → |b₂ i/logSineA s^(2*q (i.val+1))-1| ≤ ε) :
    (∏ i : Fin m, if i.val < k then b₁ i else b₂ i) ≤
      Real.exp (lambda s*(2*(FineScales.countPrefix q m : ℝ)-
        (FineScales.countPrefix q k : ℝ))+(m : ℝ)*ε) := by
  have he (i : Fin m) : (if i.val < k then b₁ i else b₂ i) ≤
      Real.exp (ε + if i.val < k then lambda s*(q (i.val+1) : ℝ)
        else lambda s*(2*(q (i.val+1) : ℝ))) := by
    by_cases hi : i.val < k
    · simpa only [if_pos hi] using positive_normalizer_power_bound s ε (b₁ i) hs _ (he₁ i hi)
    · simpa only [if_neg hi, Nat.cast_mul, Nat.cast_ofNat] using
        positive_normalizer_power_bound s ε (b₂ i) hs _ (he₂ i (by omega))
  calc
    _ ≤ ∏ i : Fin m, Real.exp (ε + if i.val < k then lambda s*(q (i.val+1) : ℝ)
        else lambda s*(2*(q (i.val+1) : ℝ))) := by
      apply Finset.prod_le_prod
      · intro i _
        split
        · exact hb₁ i
        · exact hb₂ i
      · intro i _
        exact he i
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_add_distrib, mixed_count_exponent m k hkm q]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

#print axioms truncated_fine_count_sum
#print axioms mixed_count_exponent
#print axioms mixed_normalizer_product_bound
end ConditionalSpectralAudit.FourierHarmonic
