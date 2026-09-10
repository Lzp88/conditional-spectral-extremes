import ActualRegularCoarseMinorization
import ActualEndpointChainIntegral
import PolynomialBoxCost

/-! A polynomial lower mass for the actual integrated endpoint chain.
This includes the terminal factor exp(-smax); the independent probability
regrouping module identifies this chain with a subset of innerPathEvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales ReservoirScale

theorem actual_regular_endpoint_chain_polynomial (κmin κmax K_E C_E : ℝ)
    (hκmin : 0 < κmin) (horder : κmin ≤ κmax) (hKE : 0 ≤ K_E) (hCE : 0 ≤ C_E) :
    ∃ B₀ D₀ Cstar : ℝ, 0 < B₀ ∧ 0 < D₀ ∧ 0 < Cstar ∧
    ∀ A₀ rStar gStar : ℝ, 0 < A₀ → 0 < rStar → 0 < gStar →
      64*criticalPoint κmin*gStar+1 ≤ rStar →
    let p : Parameters := ⟨A₀, rStar, D₀⟩
    ∀ᶠ n : ℕ in atTop, ∀ κ ∈ Icc κmin κmax, ∀ η : ℝ, ∀ q : ℕ → ℕ,
      Regular p n κ η K_E C_E q →
        Real.exp (-Cstar*ell n) ≤ Real.exp (-criticalPoint κmin)*
          (actualEndpointChain p n κ (gStar*ell n) B₀ q).toReal := by
  obtain ⟨B₀, D₀, c, C, hB₀, hD₀, hc, hC, hminor⟩ :=
    actual_regular_coarse_minorization κmin κmax K_E hκmin horder hKE
  let C_B := 2/Real.log 2+3
  let Ecost := 5*((1+3*C_E)*C_B+2+2*D₀)
  let Cstar := |Real.log c| * C_B+C*Ecost+|Real.log (1/5 : ℝ)| + criticalPoint κmin+1
  have hCB : 0 < C_B := by dsimp [C_B]; have hlog := Real.log_pos (by norm_num : (1 : ℝ)<2); positivity
  have hEcost : 0 < Ecost := by dsimp [Ecost]; positivity
  have hCstar : 0 < Cstar := by dsimp [Cstar]; have hs := criticalPoint_pos hκmin; positivity
  refine ⟨B₀, D₀, Cstar, hB₀, hD₀, hCstar, ?_⟩
  intro A₀ rStar gStar hA₀ hrStar hgStar hrg
  let p : Parameters := ⟨A₀, rStar, D₀⟩
  have hm := hminor A₀ rStar gStar hA₀ hrStar hgStar hrg
  filter_upwards [hm, eventually_coarse_scale_geometry p hA₀ hrStar hD₀,
    (groupNumber_tendsto_atTop p hA₀ hrStar hD₀).eventually_ge_atTop 1,
    eventually_regular_groupSamples p hA₀ hrStar hD₀ κmin κmax K_E hκmin 3,
    eventually_aStar_le_L, ell_tendsto_atTop.eventually_ge_atTop 1,
    L_tendsto_atTop.eventually_gt_atTop 0]
    with n hmn hgeom hB hcounts ha hell hL κ hκ η q hreg
  have hκp := hκmin.trans_le hκ.1
  have hcount (j : ℕ) (hj : j < groupNumber p n) : 3 ≤ groupSamples p n q j :=
    (hcounts κ hκ η C_E q hreg j hj).1
  have hH (j : ℕ) (hj : j < groupNumber p n) : 0 < groupWidth p n j :=
    hgeom.2.1.trans_le (groupWidth_ge_base p n j hgeom.1 hgeom.2.1 (by omega) hj)
  have hprod := actualEndpointChain_product_lower p n κ (gStar*ell n) B₀ c C q
    hκp hc.le hcount (hmn κ hκ η C_E q hreg)
  rw [actual_endpoint_width_cancellation p n κ (gStar*ell n) B₀ c C q (by omega) hH] at hprod
  have hrpos : 0 < r p n := by
    have hellp : 0 < ell n := lt_of_lt_of_le zero_lt_one hell
    exact mul_pos hrStar hellp
  have henergy := regular_groupU_logarithmic p n κ η K_E C_E C_B q hreg hgeom.1 hgeom.2.1
    (by omega) hCE hD₀.le hell hrpos.ne' hgeom.2.2.2.2.2
  have hjlast : groupNumber p n-1 < groupNumber p n := by omega
  have hHlast := hH (groupNumber p n-1) hjlast
  have hHlastL : groupWidth p n (groupNumber p n-1) ≤ L n := by
    have hh := groupWidth_le_distance p n (groupNumber p n-1) hgeom.2.2.2.1
      (by omega) hgeom.1.le hjlast
    linarith
  have hHexp : groupWidth p n (groupNumber p n-1) ≤ Real.exp (ell n) := by
    simpa only [ell, Real.exp_log hL] using hHlastL
  have hp : (1 : ℝ) ≤ 2^(groupNumber p n-1) := one_le_pow₀ (by norm_num)
  have hcost : c^(groupNumber p n)*(1/5)/Real.sqrt (groupWidth p n (groupNumber p n-1))*
      Real.exp (-C*(∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)) ≤
        (actualEndpointChain p n κ (gStar*ell n) B₀ q).toReal := by
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ c^(groupNumber p n)*(1/5)/
        Real.sqrt (groupWidth p n (groupNumber p n-1))*
          Real.exp (-C*(∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)) by positivity)
    simp only [mul_one] at hh
    have hid : (c^(groupNumber p n)*(1/5)/Real.sqrt (groupWidth p n (groupNumber p n-1))*
        Real.exp (-C*(∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)))*
          2^(groupNumber p n-1) =
      c^(groupNumber p n)*(2^(groupNumber p n-1)*(1/5)/Real.sqrt (groupWidth p n (groupNumber p n-1)))*
        Real.exp (-C*(∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)) := by ring
    rw [hid] at hh
    exact hh.trans hprod
  have hexp := polynomial_box_cost (ell n) (groupWidth p n (groupNumber p n-1))
    (∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)
    c C Ecost C_B (criticalPoint κmin) (1/5) (groupNumber p n) hell hHlast hHexp hc hC.le
    (criticalPoint_pos hκmin).le (by norm_num) hgeom.2.2.2.2.2 henergy
  have hweighted := mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg (-criticalPoint κmin))
  apply hexp.trans
  convert! hweighted using 1
  ring

#print axioms actual_regular_endpoint_chain_polynomial

end ConditionalSpectralExtremes.CoarseBoxes
