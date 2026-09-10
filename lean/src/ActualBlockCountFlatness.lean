import ActualBlockCountComparison
import ActualReservoirFlatness
import ActualNormalizationBounds

/-! The proved analytic reservoir flatness applied to actual finite block
counts. The threshold and constants are simultaneous in the number of blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale

theorem actual_block_counts_flatness
    {a B c D : ℝ} (ha : 0 < a) (haB : a ≤ B) (hc : 0 < c) (hcD : c ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ m : ℕ, ∀ block : ShortIndex n (cutoff n) → Fin (m+1),
      ∀ q : Fin (m+1) → ℕ, ∀ l : ℕ, (∑ j, q j)+l = k →
        c ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ D →
        let ε := C*((ell n)⁻¹+(L n)^(-3 : ℤ))
        let r := reservoirCoefficient n (cutoff n) n l
        0 < r ∧
        (1-ε)*(r/coefficient n k)*blockWeightProduct n (cutoff n) block q ≤
          actualBlockCountProbability n (cutoff n) k block q l ∧
        actualBlockCountProbability n (cutoff n) k block q l ≤
          (1+ε)*(r/coefficient n k)*blockWeightProduct n (cutoff n) block q := by
  have hB : 0 ≤ B := (ha.trans_le haB).le
  obtain ⟨C, hC, hflat⟩ := actual_reservoir_flatness hc hcD hB
  obtain ⟨N, hN, hcoef⟩ := actual_normalization_factor_bounds ha haB
  refine ⟨C, hC, ?_⟩
  filter_upwards [hflat, eventually_short_mass_half hB, eventually_ge_atTop N,
    cutoff_tendsto_atTop.eventually_ge_atTop 1, L_tendsto_atTop.eventually_gt_atTop 0,
    ell_tendsto_atTop.eventually_gt_atTop 0] with n hf hm hn hb hL hell
  intro k hak hkB m block q l hqk hlc hlD
  dsimp only
  have hkreal : (k : ℝ) ≤ B*L n := (div_le_iff₀ hL).mp hkB
  have hmass : ((cutoff n*k : ℕ) : ℝ) ≤ B*L n*cutoff n := by
    rw [Nat.cast_mul]
    nlinarith [show (0 : ℝ) ≤ cutoff n by positivity]
  have hbn : cutoff n*k ≤ n := by have := hm (cutoff n*k) hmass; omega
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k hb).trans hbn
  have hk1 : 1 ≤ k := by
    have hkpos : 0 < (k : ℝ) := (div_pos_iff_of_pos_right hL).mp (ha.trans_le hak)
    have : 0 < k := by exact_mod_cast hkpos
    omega
  have hcoefp : 0 < coefficient n k :=
    (mul_pos (by norm_num : (0 : ℝ) < 1/2) (normalizationLeading_pos (hN.trans hn) hk1)).trans_le
      (hcoef n hn k hak hkB).1
  have hd0 : ((0 : ℕ) : ℝ) ≤ B*L n*cutoff n := by
    simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg hB hL.le) (Nat.cast_nonneg (cutoff n) : (0 : ℝ) ≤ cutoff n)
  have hr := (hf 0 hd0 l hlc hlD).1
  refine ⟨hr, actual_block_count_comparison n (cutoff n) k block q l hqk hkn hbn
    (C*((ell n)⁻¹+(L n)^(-3 : ℤ))) _ (by positivity) hr hcoefp ?_⟩
  intro d hd
  have hdd : (d : ℝ) ≤ B*L n*cutoff n :=
    (by exact_mod_cast hd : (d : ℝ) ≤ (cutoff n*k : ℕ)).trans hmass
  exact (hf d hdd l hlc hlD).2

#print axioms actual_block_counts_flatness

end ConditionalSpectralExtremes.BlockCounts
