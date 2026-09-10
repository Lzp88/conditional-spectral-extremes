import ActualPoissonEnergy
import CoarsePoissonTail
import RegularBoxCountAsymptotics

/-! The actual Poisson coarse environments satisfy the manuscript's
uniform maximum condition with a constant chosen before the scale parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale FineScales

theorem actual_poisson_environment_max_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
        (Measure.pi (fun i => poissonMeasure (finePoissonRates p n k hp i))).real
          {X | ∃ j : Fin (groupNumber p n),
            regularMaximumConstant B*Real.sqrt (Real.log (ell n)) ≤
              coarseCountEnvironment p n ((k : ℝ)/L n) j X} < ε := by
  let C := regularRateConstant B
  let K := regularMaximumConstant B
  let G : ℝ := 2/Real.log 2+3
  have hB : 0 < B := ha.trans_le haB
  have hC1 : 1 ≤ C := by dsimp only [C, regularRateConstant]; linarith
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hK : 0 < K := by dsimp only [K, regularMaximumConstant]; positivity
  have hK8 : 8 ≤ K := by
    have hh : 1 ≤ Real.sqrt C := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hC1
    change 8 ≤ 8*Real.sqrt C
    linarith
  have hlog : Tendsto (fun n : ℕ => Real.log (ell n)) atTop atTop :=
    Real.tendsto_log_atTop.comp ell_tendsto_atTop
  have hscale : Tendsto (fun n : ℕ => K*Real.sqrt (Real.log (ell n))/Real.sqrt (baseWidth p n)) atTop (𝓝 0) := by
    have hh := (CoarseBoxes.sqrt_log_ell_div_sqrt_baseWidth_tendsto_zero p hr.ne').const_mul K
    simpa only [mul_zero, mul_div_assoc] using hh
  have htail : Tendsto (fun n : ℕ => 2*G*Real.exp (-3*Real.log (ell n))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
    simpa only [Function.comp_apply, mul_zero, neg_mul] using hh.const_mul (2*G)
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    eventually_coarse_scale_geometry p hA hr hD,
    hscale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually_ge_atTop 1, ell_tendsto_atTop.eventually_gt_atTop 1,
    htail.eventually (gt_mem_nhds hε)] with n hd hg hscale hlogn hell htailn
  intro hp k hak hkB
  let x : ℝ := K*Real.sqrt (Real.log (ell n))
  have hH (j : Fin (groupNumber p n)) : 0 < groupWidth p n j := zero_lt_one.trans_le (hd.widthOne j)
  have hx4 : 4 ≤ x := by
    have hs : 1 ≤ Real.sqrt (Real.log (ell n)) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogn
    have hh := mul_le_mul_of_nonneg_left hs hK.le
    change K*1 ≤ x at hh
    linarith
  have hxH (j : Fin (groupNumber p n)) : x-2 ≤ Real.sqrt (groupWidth p n j) := by
    have hs : 0 < Real.sqrt (baseWidth p n) := Real.sqrt_pos.mpr hg.2.1
    have hxbase : x ≤ Real.sqrt (baseWidth p n) := by
      have hh := (div_le_iff₀ hs).mp hscale.le
      change x ≤ 1*Real.sqrt (baseWidth p n) at hh
      simpa only [one_mul] using hh
    have hbase := groupWidth_ge_base p n j hg.1 hg.2.1 hd.enoughBlocks j.isLt
    exact (sub_le_self x (by norm_num : (0 : ℝ) ≤ 2)).trans (hxbase.trans (Real.sqrt_le_sqrt hbase))
  have hUpper (j : Fin (groupNumber p n)) :
      (∑ i, (finePoissonRates p n k hp (coarseCountIndex p n hd.basePos hd.enoughBlocks j i) : ℝ)) ≤ C*groupWidth p n j := by
    apply (hd.rateBounds k hak hkB j).2.1.trans
    dsimp only [C, regularRateConstant]
    nlinarith [hH j]
  have hpTail := coarsePoisson_environment_max_tail p n hd.basePos hd.enoughBlocks
    ((k : ℝ)/L n) C hC1 (finePoissonRates p n k hp) hH
    (fun j => zero_lt_one.trans_le (hd.rateBounds k hak hkB j).1) hUpper
    (fun j => (hd.rateBounds k hak hkB j).2.2) x (by linarith) hxH
  have hKsq : K^2=64*C := by
    change (8*Real.sqrt C)^2=64*C
    rw [mul_pow, Real.sq_sqrt hC.le]
    norm_num
  have hxsq : x^2=64*C*Real.log (ell n) := by
    dsimp only [x]
    rw [mul_pow, hKsq, Real.sq_sqrt (by linarith : 0 ≤ Real.log (ell n))]
  have hgauss : 4*Real.log (ell n) ≤ (x-2)^2/(4*C) := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ x/2) (by linarith : x/2 ≤ x-2) 2
    apply (le_div_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith
  have he : Real.exp (-(x-2)^2/(4*C)) ≤ Real.exp (-4*Real.log (ell n)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have heq : 2*G*ell n*Real.exp (-4*Real.log (ell n)) = 2*G*Real.exp (-3*Real.log (ell n)) := by
    calc
      _ = 2*G*(Real.exp (Real.log (ell n))*Real.exp (-4*Real.log (ell n))) := by
        rw [Real.exp_log (by linarith : 0 < ell n)]
        ring
      _ = _ := by rw [← Real.exp_add, show Real.log (ell n)+ -4*Real.log (ell n) = -3*Real.log (ell n) by ring]
  calc
    _ ≤ 2*(groupNumber p n : ℝ)*Real.exp (-(x-2)^2/(4*C)) := hpTail
    _ ≤ 2*G*ell n*Real.exp (-4*Real.log (ell n)) :=
      mul_le_mul (by have hh := hg.2.2.2.2.2; change (groupNumber p n : ℝ) ≤ G*ell n at hh; nlinarith)
        he (Real.exp_nonneg _) (by positivity)
    _ = _ := heq
    _ < ε := htailn

#print axioms actual_poisson_environment_max_tendsto

end ConditionalSpectralExtremes.BlockCounts
