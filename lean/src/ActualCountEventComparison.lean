import ActualCountEvents
import ActualCountTypicality
import FiniteProbabilityComparison

/-! Uniform comparison of arbitrary actual count events, including events
depending on a growing number of the manuscript's blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

theorem actual_and_multinomial_event_comparison {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ m : ℕ, ∀ block : ShortIndex n (cutoff n) → Fin (m+1),
      ∀ A : (Option (Fin (m+1)) → ℕ) → Prop,
        |conditionalProbability n k (fun s => A (profileBlockCounts block s))-
          multinomialProbability (reservoirReferenceProbabilities
            (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k
            (fun c => A (fun j => (c.val j).val))| < ε := by
  classical
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN, hnorm⟩ := actual_normalization_factor_bounds ha haB
  filter_upwards [actual_multinomial_count_comparison ha haB δ hδ,
    actual_and_reference_count_typicality ha haB δ hδ,
    eventually_ge_atTop N, L_tendsto_atTop.eventually_gt_atTop 0,
    T_tendsto_atTop.eventually_gt_atTop 0, eventually_four_cutoff_le_n]
      with n hcmp htyp hn hL hT hb
  intro k hak hkB m block A
  let p := reservoirReferenceProbabilities (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)
  let u : countFiber (Option (Fin (m+1))) k k → ℝ := fun c =>
    actualBlockCountProbability n (cutoff n) k block (fun j => (c.val (some j)).val) (c.val none).val
  let v := multinomialMass p k
  let E : countFiber (Option (Fin (m+1))) k k → Prop :=
    fun c => TypicalReservoirCount n ((k : ℝ)/L n) (c.val none).val
  have hu : ∀ c, 0 ≤ u c := fun c => actualBlockCountProbability_nonneg _ _ _ _ _ _
  have hH := shortBlockHarmonicMass_nonneg n (cutoff n) block
  have hp : ∀ j, 0 ≤ p j := reservoirReferenceProbabilities_nonneg _ _ _ hH hT.le hL.le
  have hsumH : (∑ j, shortBlockHarmonicMass n (cutoff n) block j)+T n = L n := by
    rw [shortBlockHarmonicMass_sum n (cutoff n) (by omega) block]
    unfold T
    ring
  have hsum : ∑ j, p j = 1 := reservoirReferenceProbabilities_sum _ _ _ hL.ne' hsumH
  have hv : ∀ c, 0 ≤ v c := multinomialMass_nonneg hp k
  have hvsum : ∑ c, v c = 1 := multinomialMass_sum_one p hsum k
  have hkp : 0 < (k : ℝ) := (mul_pos ha hL).trans_le ((le_div_iff₀ hL).mp hak)
  have hk1 : 1 ≤ k := by
    have : 0 < k := by exact_mod_cast hkp
    omega
  have hcoef : 0 < coefficient n k :=
    (mul_pos (by norm_num : (0 : ℝ) < 1/2) (normalizationLeading_pos (hN.trans hn) hk1)).trans_le
      (hnorm n hn k hak hkB).1
  have husum : ∑ c, u c = 1 := actualBlockCountProbability_sum_one _ _ _ _ hcoef
  have huc : (∑ c, if ¬E c then u c else 0)+(∑ c, if E c then u c else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← husum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : E c <;> simp [hc]
  have huvtyp := htyp k hak hkB m block
  have hutyp : 1-δ < ∑ c, if E c then u c else 0 := by
    simpa only [E, u, actual_count_typical_sum] using huvtyp.2
  have hutail : (∑ c, if ¬E c then u c else 0) < δ := by linarith
  have hvcomp := multinomialProbability_complement p hsum k E
  have hvtail : (∑ c, if ¬E c then v c else 0) < δ := by
    have ht : multinomialProbability p k (fun c => ¬E c) < δ := by
      have hvtyp : 1-δ < multinomialProbability p k E := huvtyp.1
      linarith
    convert ht using 1
    apply Finset.sum_congr (Finset.ext (by simp))
    intro c _
    by_cases hc : E c <;> simp [hc, v]
  have hh := finite_event_comparison u v hu hv hvsum E
    (fun c => A (fun j => (c.val j).val)) δ hδ.le (fun c hc => hcmp k hak hkB m block c hc)
  have hf : δ+(∑ c, if ¬E c then u c else 0)+(∑ c, if ¬E c then v c else 0) < ε := by
    dsimp [δ] at *
    linarith
  have he := hh.trans_lt hf
  simpa only [u, v, actual_count_event_sum, multinomialProbability] using he

#print axioms actual_and_multinomial_event_comparison

end ConditionalSpectralExtremes.BlockCounts
