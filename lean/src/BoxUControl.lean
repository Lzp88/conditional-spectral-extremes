import RegularBoxEnergy

/-! Pointwise control by the actual five-term U_j used in the manuscript. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem paddedE_ge_one (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) (j : ℕ) :
    1 ≤ paddedE p n κ q j := by
  unfold paddedE
  split
  · exact le_rfl
  · exact localE_ge_one _ _ _ _ _

theorem groupU_controls_terms (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (j : ℕ) :
    1 ≤ groupU p n κ q j ∧
      paddedE p n κ q j ≤ groupU p n κ q j ∧
      paddedE p n κ q (j+1) ≤ groupU p n κ q j ∧
      paddedE p n κ q (j+2) ≤ groupU p n κ q j ∧
      boxBoundaryCost (groupNumber p n) (fun i => groupWidth p n (i-1)) (r p n) j ≤
        groupU p n κ q j := by
  have h0 := paddedE_ge_one p n κ q j
  have h1 := paddedE_ge_one p n κ q (j+1)
  have h2 := paddedE_ge_one p n κ q (j+2)
  have hb : 0 ≤ boxBoundaryCost (groupNumber p n)
      (fun i => groupWidth p n (i-1)) (r p n) j := by
    unfold boxBoundaryCost
    split
    · exact div_nonneg hr (Real.sqrt_nonneg _)
    · exact le_rfl
  unfold groupU dyadicBoxU
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem groupU_controls_environment (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (j : ℕ) (hj : j < groupNumber p n) :
    environmentE p n κ q j ≤ groupU p n κ q j := by
  simpa only [paddedE_succ p n κ q j hj] using (groupU_controls_terms p n κ q hr j).2.2.1

theorem groupU_controls_left_environment (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (j : ℕ) (hj0 : 0 < j) (hj : j < groupNumber p n) :
    environmentE p n κ q (j-1) ≤ groupU p n κ q j := by
  have hh := (groupU_controls_terms p n κ q hr j).2.1
  have hp : paddedE p n κ q j=environmentE p n κ q (j-1) := by
    unfold paddedE
    rw [if_neg (by omega)]
  rwa [hp] at hh

theorem groupU_controls_right_environment (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (j : ℕ) (hj : j+1 < groupNumber p n) :
    environmentE p n κ q (j+1) ≤ groupU p n κ q j := by
  have hh := (groupU_controls_terms p n κ q hr j).2.2.2.1
  have hp : paddedE p n κ q (j+2)=environmentE p n κ q (j+1) := by
    simpa only [Nat.add_assoc] using paddedE_succ p n κ q (j+1) hj
  rwa [hp] at hh

theorem groupU_controls_boundary (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (j : ℕ) (hb : j=0 ∨ j+1=groupNumber p n)
    (hH : 0 < groupWidth p n j) :
    r p n ≤ Real.sqrt (groupWidth p n j)*groupU p n κ q j := by
  have hh := (groupU_controls_terms p n κ q hr j).2.2.2.2
  unfold boxBoundaryCost at hh
  rw [if_pos hb] at hh
  simp only [Nat.add_sub_cancel] at hh
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hH)).1 hh |>.trans_eq (by ring)

#print axioms paddedE_ge_one
#print axioms groupU_controls_terms
#print axioms groupU_controls_environment
#print axioms groupU_controls_left_environment
#print axioms groupU_controls_right_environment
#print axioms groupU_controls_boundary

end ConditionalSpectralExtremes.CoarseBoxes
