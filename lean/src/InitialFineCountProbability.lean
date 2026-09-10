import FineCountDefinitions
import FineHarmonicAsymptotics
import MultinomialEventBounds
import ActualCountEventComparison

/-! The initial short block has O(r) cycles with high probability under
both the actual reference law and the actual fixed-cycle profile law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

theorem eventually_initial_harmonicMass_le (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) :
    ∀ᶠ n : ℕ in atTop, fineHarmonicMass p n 0 ≤ 2*r p n := by
  filter_upwards [eventually_fine_scale_geometry p hA hr,
    (r_tendsto_atTop p hr).eventually_ge_atTop (Real.eulerMascheroniConstant+1),
    cutoff_tendsto_atTop.eventually_ge_atTop 1, eventually_four_cutoff_le_n] with n hg hh hcut hcn
  have hω : 0 < omega p n := by
    have hlow := hg.2.2.2.2.1
    have hp := hg.1
    change 0 < p.A₀*ell n at hp
    linarith
  rw [fineHarmonicMass_initial p n hω hg.2.2.2.1 (by omega) (by omega)]
  have he := (abs_le.mp (harmonic_floor_exp_error (r p n) hg.2.2.1)).2
  have hexp : Real.exp (-r p n) ≤ 1/2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hg.2.2.1)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  linarith

theorem reference_initial_count_failure_bound (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) {a B : ℝ}
    (ha : 0 < a) (haB : a ≤ B) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
        multinomialProbability (fineReferenceProbabilities p n) k
          (fun c => 6*B*r p n < ((c.val (some 0)).val : ℝ)) ≤ Real.exp (-2*B*r p n) := by
  have hB : 0 < B := ha.trans_le haB
  filter_upwards [eventually_initial_harmonicMass_le p hA hr,
    (r_tendsto_atTop p hr).eventually_gt_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0, T_tendsto_atTop.eventually_gt_atTop 0,
    eventually_four_cutoff_le_n] with n hmass hrn hL hT hb
  intro k hak hkB
  let v := fineReferenceProbabilities p n
  have hv : ∀ j, 0 ≤ v j := reservoirReferenceProbabilities_nonneg _ _ _
    (shortBlockHarmonicMass_nonneg n (cutoff n) (fineCategoryBlock p n)) hT.le hL.le
  have hsumH : (∑ j, fineHarmonicMass p n j)+T n = L n := by
    rw [show (∑ j, fineHarmonicMass p n j) = harmonicNumber (cutoff n) from
      shortBlockHarmonicMass_sum n (cutoff n) (by omega) (fineCategoryBlock p n)]
    unfold T
    ring
  have hsum : ∑ j, v j = 1 := reservoirReferenceProbabilities_sum _ _ _ hL.ne' hsumH
  have hκ : 0 < (k : ℝ)/L n := ha.trans_le hak
  have heq : (k : ℝ)*v (some 0) = ((k : ℝ)/L n)*fineHarmonicMass p n 0 := by
    dsimp [v, fineReferenceProbabilities, reservoirReferenceProbabilities, reservoirReferenceWeights]
    ring
  have hμ : 0 ≤ (k : ℝ)*v (some 0) := mul_nonneg (Nat.cast_nonneg _) (hv _)
  have hμB : (k : ℝ)*v (some 0) ≤ 2*B*r p n := by
    rw [heq]
    have hh := mul_le_mul hkB hmass (shortBlockHarmonicMass_nonneg n (cutoff n) (fineCategoryBlock p n) 0) hB.le
    nlinarith
  have hh := multinomial_upper_chernoff v hv hsum k (some 0) (6*B*r p n) 1 (by norm_num)
  have hg := multinomial_mgf_le_poisson v hv hsum k (some 0) 1
  have htail : multinomialProbability v k (fun c => 6*B*r p n ≤ ((c.val (some 0)).val : ℝ)) ≤
      Real.exp (-2*B*r p n) := by
    calc
      _ ≤ Real.exp (-(1 : ℝ)*(6*B*r p n))*(1-v (some 0)+v (some 0)*Real.exp 1)^k := hh
      _ ≤ Real.exp (-(1 : ℝ)*(6*B*r p n))*Real.exp ((k : ℝ)*v (some 0)*(Real.exp 1-1)) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_nonneg _)
      _ = Real.exp (-(1 : ℝ)*(6*B*r p n)+(k : ℝ)*v (some 0)*(Real.exp 1-1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_left (Real.exp_one_lt_three.le) hμ
        nlinarith
  exact (multinomialProbability_mono v hv k _ _ (fun _ hc => hc.le)).trans htail

theorem actual_initial_count_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) {a B : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      conditionalProbability n k (fun s => 6*B*r p n <
        (profileBlockCounts (fineCategoryBlock p n) s (some 0) : ℝ)) < ε := by
  have hB : 0 < B := ha.trans_le haB
  have he : 0 < ε/2 := by positivity
  have ht : Tendsto (fun n => Real.exp (-2*B*r p n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_assoc] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ((r_tendsto_atTop p hr).const_mul_atTop (show 0 < 2*B by positivity))
  filter_upwards [reference_initial_count_failure_bound p hA hr ha haB,
    actual_and_multinomial_event_comparison ha haB (ε/2) he,
    ht.eventually (gt_mem_nhds he)] with n href hcmp ht
  intro k hak hkB
  have hp := (href k hak hkB).trans_lt ht
  have hc := hcmp k hak hkB (count p n) (fineCategoryBlock p n)
    (fun q => 6*B*r p n < (q (some 0) : ℝ))
  have hd : |conditionalProbability n k (fun s => 6*B*r p n <
      (profileBlockCounts (fineCategoryBlock p n) s (some 0) : ℝ))-
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => 6*B*r p n < ((c.val (some 0)).val : ℝ))| < ε/2 := by
    simpa only [fineReferenceProbabilities, show fineHarmonicMass p n =
      shortBlockHarmonicMass n (cutoff n) (fineCategoryBlock p n) from rfl] using hc
  linarith [(abs_lt.mp hd).2]

#print axioms eventually_initial_harmonicMass_le
#print axioms reference_initial_count_failure_bound
#print axioms actual_initial_count_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
