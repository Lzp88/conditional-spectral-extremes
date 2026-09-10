import CoarseBoxDefinitions

/-! The summed U_j estimate instantiated at the literal fine-scale
environment and its corrected dyadic partition. -/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem paddedE_zero (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) :
    paddedE p n κ q 0 = 1 := by simp [paddedE]

theorem paddedE_last (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) :
    paddedE p n κ q (groupNumber p n+1) = 1 := by simp [paddedE]

theorem paddedE_succ (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (hj : j < groupNumber p n) :
    paddedE p n κ q (j+1) = environmentE p n κ q j := by
  rw [paddedE, if_neg (by omega), Nat.add_sub_cancel]

theorem regular_groupU_energy (p : Parameters) (n : ℕ) (κ η K_E C_E : ℝ) (q : ℕ → ℕ)
    (hreg : Regular p n κ η K_E C_E q) (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hm : 2*baseBlocks p n ≤ count p n) :
    (∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2) ≤
      5*((1+3*C_E)*groupNumber p n+2+2*(r p n)^2/baseWidth p n) := by
  have hv := baseBlocks_pos p n hω hb
  have hne := ConditionalSpectralAudit.DyadicGrouping.dyadic_groups_nonempty _ _ hv hm
  have hB : 0 < groupNumber p n := List.length_pos_iff.mpr hne
  have hH : ∀ j ∈ Finset.range (groupNumber p n),
      baseWidth p n ≤ (fun i => groupWidth p n (i-1)) (j+1) := by
    intro j hj
    simpa only [Nat.add_sub_cancel] using
      groupWidth_ge_base p n j hω hb hm (Finset.mem_range.mp hj)
  have henergy : (∑ j ∈ Finset.range (groupNumber p n), (paddedE p n κ q (j+1))^2) ≤
      C_E*groupNumber p n := by
    calc
      _ = ∑ j ∈ Finset.range (groupNumber p n), (environmentE p n κ q j)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [paddedE_succ p n κ q j (Finset.mem_range.mp hj)]
      _ ≤ _ := hreg.2.2
  exact dyadic_box_energy_regular (groupNumber p n) hB
    (fun i => groupWidth p n (i-1)) (paddedE p n κ q) (r p n) (baseWidth p n) C_E
    hb hH (paddedE_zero p n κ q) (paddedE_last p n κ q) henergy

theorem regular_groupU_logarithmic (p : Parameters) (n : ℕ) (κ η K_E C_E C_B : ℝ) (q : ℕ → ℕ)
    (hreg : Regular p n κ η K_E C_E q) (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hm : 2*baseBlocks p n ≤ count p n) (hCE : 0 ≤ C_E) (hD : 0 ≤ p.D₀)
    (hℓ : 1 ≤ ReservoirScale.ell n) (hr : r p n ≠ 0)
    (hgroups : (groupNumber p n : ℝ) ≤ C_B*ReservoirScale.ell n) :
    (∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2) ≤
      (5*((1+3*C_E)*C_B+2+2*p.D₀))*ReservoirScale.ell n := by
  have hh := regular_groupU_energy p n κ η K_E C_E q hreg hω hb hm
  have hbase : (r p n)^2/baseWidth p n = p.D₀*Real.log (ReservoirScale.ell n) :=
    dyadic_boundary_cost_base_scale (r p n) p.D₀ (ReservoirScale.ell n) hr
  have hlog : Real.log (ReservoirScale.ell n) ≤ ReservoirScale.ell n :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hg := mul_le_mul_of_nonneg_left hgroups (show 0 ≤ 1+3*C_E by positivity)
  have hl := mul_le_mul_of_nonneg_left hlog hD
  rw [show 2*(r p n)^2/baseWidth p n=2*((r p n)^2/baseWidth p n) by ring, hbase] at hh
  nlinarith

#print axioms paddedE_zero
#print axioms paddedE_last
#print axioms paddedE_succ
#print axioms regular_groupU_energy
#print axioms regular_groupU_logarithmic

end ConditionalSpectralExtremes.CoarseBoxes
