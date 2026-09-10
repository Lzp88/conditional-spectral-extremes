import ActualNormalizationAsymptotic

/-! Uniform positive bounds for the actual fixed-cycle normalization, with no extra feasibility premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem gamma_two_sided_on_positive_interval {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ g G : ℝ, 0 < g ∧ 0 < G ∧ ∀ s ∈ Icc a B, g ≤ Real.Gamma s ∧ Real.Gamma s ≤ G := by
  have hc : ContinuousOn Real.Gamma (Icc a B) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun s hs => ha.trans_le hs.1)
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 haB) hc
  obtain ⟨G, hG, hmax⟩ := gamma_bounded_on_positive_interval ha haB
  exact ⟨Real.Gamma s, G, Real.Gamma_pos_of_pos (ha.trans_le hs.1), hG,
    fun t ht => ⟨hmin ht, hmax t ht⟩⟩

def normalizationLeading (n k : ℕ) : ℝ :=
  (Real.log n) ^ k / ((n : ℝ) * k.factorial * Real.Gamma ((k : ℝ) / Real.log n))

theorem normalizationLeading_pos {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    0 < normalizationLeading n k := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hG := Real.Gamma_pos_of_pos (div_pos hkp hL)
  unfold normalizationLeading
  positivity

theorem actual_normalization_factor_bounds {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : ℕ,
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      (1 / 2 : ℝ) * normalizationLeading n k ≤ coefficient n k ∧
        coefficient n k ≤ (3 / 2 : ℝ) * normalizationLeading n k := by
  obtain ⟨C, hC, N, hN, he⟩ := actual_normalization_relative_error ha haB
  have hLtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N', hN'⟩ := eventually_atTop.1 (hLtop.eventually_ge_atTop (2 * C))
  refine ⟨max N N', hN.trans (le_max_left _ _), ?_⟩
  intro n hn k hak hkB
  have hnN := (le_max_left N N').trans hn
  have hn2 : 2 ≤ n := hN.trans hnN
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hk1 : 1 ≤ k := by
    have hkp : 0 < (k : ℝ) := by
      have hi := (le_div_iff₀ hL).1 hak
      exact (mul_pos ha hL).trans_le hi
    have : 0 < k := by exact_mod_cast hkp
    omega
  have hhalf : C / Real.log n ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hL).2 (by have := hN' n ((le_max_right N N').trans hn); linarith)
  have hb := abs_le.mp ((he n hnN k hk1 hak hkB).trans hhalf)
  have hp := normalizationLeading_pos hn2 hk1
  change -(1 / 2 : ℝ) ≤ coefficient n k / normalizationLeading n k - 1 ∧
    coefficient n k / normalizationLeading n k - 1 ≤ (1 / 2 : ℝ) at hb
  constructor
  · apply (le_div_iff₀ hp).1
    linarith [hb.1]
  · apply (div_le_iff₀ hp).1
    linarith [hb.2]

#print axioms actual_normalization_factor_bounds
end ConditionalSpectralExtremes
