import MultinomialReservoirReference
import ActualBlockCountFlatness
import ReservoirMultinomialScale

/-! The actual conditional count mass is uniformly relatively equivalent to
the manuscript's multinomial mass on its typical long-count window. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

theorem reservoir_scale_weight_identity {κ : Type*} [Fintype κ]
    (n k : ℕ) (block : ShortIndex n (cutoff n) → κ)
    (c : countFiber (Option κ) k k) (hL : 0 < L n) (hT : 0 < T n) :
    (reservoirCoefficient n (cutoff n) n (c.val none).val / coefficient n k)*
      blockWeightProduct n (cutoff n) block (fun j => (c.val (some j)).val) =
    reservoirMultinomialScale n k (c.val none).val *
      multinomialMass (reservoirReferenceProbabilities
        (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k c := by
  rw [reservoirReference_multinomialMass]
  let l := (c.val none).val
  have hf : ((L n)^k*(l.factorial : ℝ)/((T n)^l*(k.factorial : ℝ))) *
      ((k.factorial : ℝ)/(L n)^k*((T n)^l/(l.factorial : ℝ))) = 1 := by field_simp
  unfold reservoirMultinomialScale blockWeightProduct
  dsimp only [l] at hf
  calc
    _ = (reservoirCoefficient n (cutoff n) n (c.val none).val/coefficient n k)*
        (((L n)^k*((c.val none).val.factorial : ℝ)/((T n)^(c.val none).val*(k.factorial : ℝ))) *
        ((k.factorial : ℝ)/(L n)^k*((T n)^(c.val none).val/((c.val none).val.factorial : ℝ)))) *
        ∏ j, shortBlockHarmonicMass n (cutoff n) block j^(c.val (some j)).val /
          ((c.val (some j)).val.factorial : ℝ) := by rw [hf, mul_one]
    _ = _ := by ring

/-- Proposition multinomial's uniform relative point-mass assertion. The
number of blocks is quantified after the eventual threshold. -/
theorem actual_multinomial_count_comparison {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ m : ℕ, ∀ block : ShortIndex n (cutoff n) → Fin (m+1),
      ∀ c : countFiber (Option (Fin (m+1))) k k,
        TypicalReservoirCount n ((k : ℝ)/L n) (c.val none).val →
        let P := multinomialMass (reservoirReferenceProbabilities
          (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k c
        (1-ε)*P ≤ actualBlockCountProbability n (cutoff n) k block
          (fun j => (c.val (some j)).val) (c.val none).val ∧
        actualBlockCountProbability n (cutoff n) k block
          (fun j => (c.val (some j)).val) (c.val none).val ≤ (1+ε)*P := by
  let δ : ℝ := min (ε/4) (1/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hflat⟩ := actual_block_counts_flatness ha haB
    (c := a/2) (D := 2*B) (by positivity) (by linarith)
  have he := (reservoir_flatness_error_tendsto_zero C).eventually (gt_mem_nhds hδ)
  filter_upwards [hflat, he, actual_reservoir_multinomial_scale_tendsto ha haB δ hδ,
    eventually_typical_reservoir_window ha haB 1 (by norm_num),
    L_tendsto_atTop.eventually_gt_atTop 0, T_tendsto_atTop.eventually_gt_atTop 0,
    ell_tendsto_atTop.eventually_gt_atTop 0] with n hf hsmall hscale hwindow hL hT hell
  intro k hak hkB m block c htyp
  dsimp only
  let P := multinomialMass (reservoirReferenceProbabilities
    (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k c
  let e := C*((ell n)⁻¹+(L n)^(-3 : ℤ))
  let S := reservoirMultinomialScale n k (c.val none).val
  have hP : 0 ≤ P := multinomialMass_nonneg
    (reservoirReferenceProbabilities_nonneg _ _ _ (shortBlockHarmonicMass_nonneg n (cutoff n) block) hT.le hL.le) k c
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hed : e ≤ δ := hsmall.le
  have hdhalf : δ ≤ 1/2 := min_le_right _ _
  have hdeps : δ ≤ ε/4 := min_le_left _ _
  have hSb := abs_lt.mp (hscale k hak hkB (c.val none).val htyp)
  have hS0 : 0 ≤ S := by dsimp [S]; linarith
  have hwin := (hwindow ((k : ℝ)/L n) ⟨hak, hkB⟩ (c.val none).val htyp).1
  have hb := hf k hak hkB m block (fun j => (c.val (some j)).val) (c.val none).val
    (reservoirReference_counts_sum k c) hwin.1 hwin.2
  dsimp only at hb
  have hi := reservoir_scale_weight_identity n k block c hL hT
  have hl : (1-e)*S*P ≤ actualBlockCountProbability n (cutoff n) k block
      (fun j => (c.val (some j)).val) (c.val none).val := by
    calc
      _ = (1-e)*((reservoirCoefficient n (cutoff n) n (c.val none).val/coefficient n k)*
          blockWeightProduct n (cutoff n) block (fun j => (c.val (some j)).val)) := by
        rw [hi]
        dsimp [P, S]
        ring
      _ ≤ _ := by simpa only [mul_assoc] using hb.2.1
  have hu : actualBlockCountProbability n (cutoff n) k block
      (fun j => (c.val (some j)).val) (c.val none).val ≤ (1+e)*S*P := by
    calc
      _ ≤ (1+e)*((reservoirCoefficient n (cutoff n) n (c.val none).val/coefficient n k)*
          blockWeightProduct n (cutoff n) block (fun j => (c.val (some j)).val)) := by
        simpa only [mul_assoc] using hb.2.2
      _ = _ := by
        rw [hi]
        dsimp [P, S]
        ring
  have hSl : 1-ε ≤ (1-e)*S := by
    have hs : 1-δ ≤ S := by dsimp [S]; linarith
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1-e by linarith)
    nlinarith [mul_nonneg he0 hδ.le]
  have hSu : (1+e)*S ≤ 1+ε := by
    have hs : S ≤ 1+δ := by dsimp [S]; linarith
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1+e by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hed) hδ.le,
      mul_nonneg (sub_nonneg.mpr hdhalf) hδ.le]
  exact ⟨(mul_le_mul_of_nonneg_right hSl hP).trans hl, hu.trans (mul_le_mul_of_nonneg_right hSu hP)⟩

#print axioms reservoir_scale_weight_identity
#print axioms actual_multinomial_count_comparison

end ConditionalSpectralExtremes.BlockCounts
