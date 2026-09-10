import ActualCoarseRateBounds
import CoarseCountCoupling
import CoarseGroupGrowth

/-! Uniform tightness of the discrepancy energy in the single actual
Poisson--multinomial coupling, at the literal manuscript scales. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale FineScales

theorem ell_div_sqrt_L_tendsto_zero :
    Tendsto (fun n : ℕ => ell n / Real.sqrt (L n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.sqrt_eq_rpow, ell] using
    (isLittleO_log_rpow_atTop (r := (1:ℝ)/2) (by norm_num)).tendsto_div_nhds_zero.comp L_tendsto_atTop

theorem eventually_coupling_energy_coefficient (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {B : ℝ} (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ)/L n ≤ B →
      2*Real.sqrt k*(groupNumber p n : ℝ)/L n+4*(k : ℝ)/L n ≤ 1+4*B := by
  let G : ℝ := 2/Real.log 2+3
  have hG : 0 < G := by dsimp [G]; positivity
  have ht : Tendsto (fun n : ℕ => (2*Real.sqrt B*G)*(ell n/Real.sqrt (L n))) atTop (𝓝 0) := by
    simpa using ell_div_sqrt_L_tendsto_zero.const_mul (2*Real.sqrt B*G)
  filter_upwards [eventually_coarse_scale_geometry p hA hr hD,
    L_tendsto_atTop.eventually_gt_atTop 0, ell_tendsto_atTop.eventually_ge_atTop 0,
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hg hL he hsmall
  intro k hk
  have hkn : (k : ℝ) ≤ B*L n := (div_le_iff₀ hL).mp hk
  have hs : Real.sqrt k ≤ Real.sqrt B*Real.sqrt (L n) := by
    rw [← Real.sqrt_mul hB.le]
    exact Real.sqrt_le_sqrt hkn
  have hgroups : (groupNumber p n : ℝ) ≤ G*ell n := hg.2.2.2.2.2
  have hfirst : 2*Real.sqrt k*(groupNumber p n : ℝ)/L n ≤ 1 := by
    calc
      _ ≤ 2*(Real.sqrt B*Real.sqrt (L n))*(G*ell n)/L n :=
        div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num))
          hgroups (Nat.cast_nonneg _) (by positivity)) hL.le
      _ = (2*Real.sqrt B*G*ell n)*(Real.sqrt (L n)/L n) := by ring
      _ = (2*Real.sqrt B*G)*(ell n/Real.sqrt (L n)) := by rw [Real.sqrt_div_self']; ring
      _ ≤ 1 := hsmall.le
  have hh := mul_le_mul_of_nonneg_left hk (by norm_num : (0:ℝ)≤4)
  calc
    _ = 2*Real.sqrt k*(groupNumber p n : ℝ)/L n+4*((k : ℝ)/L n) := by ring
    _ ≤ _ := add_le_add hfirst hh

theorem actual_coupling_energy_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
      (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i)
      (hs : (∑ i, fineReferenceProbabilities p n i) = 1)
      (k : ℕ), a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      (poissonMultinomialCoupling (fineReferenceProbabilities p n) hp hs k).toMeasure.real
        {z | R n ≤ coarseCouplingEnergy p n hv hm z} < ε := by
  have hB : 0 < B := ha.trans_le haB
  have ht : Tendsto (fun n => (1+4*B)/R n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hR
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    eventually_coupling_energy_coefficient p hA hr hD hB,
    hR.eventually_gt_atTop 0, ht.eventually (gt_mem_nhds hε)] with n hd hc hRn hsmall
  intro hv hm hp hs k hak hkB
  have hk : 0 < k := by
    have hkr : (0:ℝ) < k := (div_pos_iff.mp (ha.trans_le hak)).resolve_right (fun h => (not_lt.mpr hd.Lpos.le) h.2) |>.1
    exact_mod_cast hkr
  have hh := couplingWeightedDiscrepancy_uniform_tail (fineReferenceProbabilities p n) hp hs k hk
    (coarseCountSet p n hv hm) (fun j => groupWidth p n j)
    (fun j => lt_of_lt_of_le zero_lt_one (hd.widthOne j)) (L n) 2 hd.Lpos (by norm_num)
    hd.massBound hd.totalWidth (R n) hRn
  have hbound : (poissonMultinomialCoupling (fineReferenceProbabilities p n) hp hs k).toMeasure.real
        {z | R n ≤ coarseCouplingEnergy p n hv hm z} ≤
      (2*Real.sqrt k*(groupNumber p n : ℝ)/L n+4*(k : ℝ)/L n)/R n := by
    simpa only [coarseCouplingEnergy, Fintype.card_fin, show (2:ℝ)^2=4 by norm_num] using hh
  exact (hbound.trans (div_le_div_of_nonneg_right (hc k hkB) hRn.le)).trans_lt hsmall

#print axioms ell_div_sqrt_L_tendsto_zero
#print axioms eventually_coupling_energy_coefficient
#print axioms actual_coupling_energy_tendsto

end ConditionalSpectralExtremes.BlockCounts
