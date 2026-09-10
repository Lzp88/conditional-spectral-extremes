import BoxKernelConstants
import ActualCoarseKernelDefinitions
import CoarseEndpointBoxes
import ActualBoxEndpointMargins
import ActualBoxDriftBound
import BoxUAsymptotics
import CoarseGroupGrowth

/-! Actual uniform killed-kernel minorization on every regular
environment, with B_0,D_0,c,C chosen independently of fixed gStar,rStar.
All walk, bridge, count, drift, chord and large-n inputs are proved in
the imported modules and are instantiated here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales ReservoirScale

theorem actual_regular_coarse_minorization (κmin κmax K_E : ℝ)
    (hκmin : 0 < κmin) (horder : κmin ≤ κmax) (hKE : 0 ≤ K_E) :
    ∃ B₀ D₀ c C : ℝ, 0 < B₀ ∧ 0 < D₀ ∧ 0 < c ∧ 0 < C ∧
    ∀ A₀ rStar gStar : ℝ, 0 < A₀ → 0 < rStar → 0 < gStar →
      64*criticalPoint κmin*gStar+1 ≤ rStar →
    let p : Parameters := ⟨A₀, rStar, D₀⟩
    ∀ᶠ n : ℕ in atTop, ∀ κ ∈ Icc κmin κmax, ∀ η C_E : ℝ, ∀ q : ℕ → ℕ,
      Regular p n κ η K_E C_E q → ∀ j < groupNumber p n,
      ∀ x ∈ Icc (endpointLower p n κ (gStar*ell n) B₀ q j) (endpointUpper p n κ (gStar*ell n) B₀ q j),
      ∀ x' ∈ Icc (endpointLower p n κ (gStar*ell n) B₀ q (j+1)) (endpointUpper p n κ (gStar*ell n) B₀ q (j+1)),
        c/Real.sqrt (groupWidth p n j)*Real.exp (-C*(groupU p n κ q j)^2) ≤
          actualCoarseKernel p n κ (gStar*ell n) q j x x' := by
  let smin := criticalPoint κmax
  let smax := criticalPoint κmin
  let α := κmin/2
  let A := 2*κmax
  have hκmax : 0 < κmax := hκmin.trans_le horder
  have hsmin : 0 < smin := criticalPoint_pos hκmax
  have hsmax : 0 < smax := criticalPoint_pos hκmin
  have hsorder : smin ≤ smax := criticalPoint_strictAntiOn.antitoneOn hκmin hκmax horder
  have hα : 0 < α := half_pos hκmin
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨W, cb, K, δ, N, hW, hcb, hK, hδ, hkernel⟩ :=
    actual_killed_group_kernel smin smax (by linarith) hsorder
  let M := W*Real.sqrt A+2/(α*smin)
  let B₀ := 3+M
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB₀ : 0 < B₀ := by dsimp [B₀]; linarith
  obtain ⟨D₀, hD₀, hDsmall⟩ := exists_boundary_scale (M*K_E) smax hsmax
  let D := 1/(κmin*smin)+5/smin+4*B₀+4
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B₀, D₀, cb/Real.sqrt A, K*D^2/α, hB₀, hD₀, by positivity, by positivity, ?_⟩
  intro A₀ rStar gStar hA₀ hrStar hgStar hrg
  let p : Parameters := ⟨A₀, rStar, D₀⟩
  have huε : 0 < δ*α/D := by positivity
  filter_upwards [eventually_coarse_scale_geometry p hA₀ hrStar hD₀,
    (groupNumber_tendsto_atTop p hA₀ hrStar hD₀).eventually_ge_atTop 2,
    (baseWidth_tendsto_atTop p hA₀ hrStar.ne' hD₀).eventually_ge_atTop 1,
    eventually_regular_groupSamples p hA₀ hrStar hD₀ κmin κmax K_E hκmin (max (N+1) 3),
    eventually_regular_groupU_small p hA₀ hrStar hD₀ K_E (δ*α/D) huε,
    ell_tendsto_atTop.eventually_ge_atTop 2,
    (r_tendsto_atTop p hrStar).eventually_ge_atTop (2*smax)]
    with n hgeom hgroups hbase hcounts husmall hell hrlarge κ hκ η C_E q hreg j hj x hx x' hx'
  have hs := (criticalPoint_compact_bounds hκmin hκ.1 hκ.2).2
  have hκp := hκmin.trans_le hκ.1
  have hG : 0 ≤ gStar*ell n := mul_nonneg hgStar.le (by linarith)
  have hrpos : 0 ≤ r p n := (show 0 ≤ 2*smax by positivity).trans hrlarge
  have hGr : gStar*ell n ≤ r p n/(64*smax) := by
    apply (le_div_iff₀ (show 0 < 64*smax by positivity)).2
    have hh := mul_le_mul_of_nonneg_right hrg (show 0 ≤ ell n by linarith)
    change (64*smax*gStar+1)*ell n ≤ r p n at hh
    nlinarith
  have hGr' : gStar*ell n ≤ r p n/smin := hGr.trans
    (div_le_div_of_nonneg_left hrpos hsmin (by nlinarith [hsorder]))
  have hm : 2*baseBlocks p n ≤ count p n := by omega
  have hHbase := groupWidth_ge_base p n j hgeom.1 hgeom.2.1 hm hj
  have hH : 1 ≤ groupWidth p n j := hbase.trans hHbase
  have hHp : 0 < groupWidth p n j := lt_of_lt_of_le zero_lt_one hH
  have hcnt := hcounts κ hκ η C_E q hreg j hj
  have hQpos : 0 < groupSamples p n q j := by omega
  have hQreal : (0 : ℝ) < (groupSamples p n q j : ℝ) := by exact_mod_cast hQpos
  have hfree : N ≤ groupSamples p n q j-1 := by omega
  have hQeq : groupSamples p n q j-1+1=groupSamples p n q j := Nat.sub_add_cancel (by omega)
  let e := x-boxCenter p n κ (gStar*ell n) B₀ q j
  let e' := x'-boxCenter p n κ (gStar*ell n) B₀ q (j+1)
  have hxe : boxCenter p n κ (gStar*ell n) B₀ q j+e=x := by dsimp [e]; ring
  have hxe' : boxCenter p n κ (gStar*ell n) B₀ q (j+1)+e'=x' := by dsimp [e']; ring
  have hoff := actual_endpoint_offsets p n κ (gStar*ell n) B₀ q hgeom.2.2.2.1 hm hgeom.1.le j hj hH x x' hx hx'
  have hdrift := actual_box_drift_bound p n κ κmin (gStar*ell n) B₀ smin q hrpos hB₀.le
    hκmin hκ.1 hsmin hs.1 hG hGr' hgeom.2.2.2.1 hm hgeom.1.le hgroups j hj hH e e' hoff.1 hoff.2.1
  rw [hxe, hxe'] at hdrift
  have hmargin := actual_box_endpoint_margins p n κ η K_E C_E (gStar*ell n) B₀ W A α smin smax q
    hreg hKE hG hW.le hA.le hα hsmin hs.1 hs.2 (by dsimp [B₀, M]; linarith)
    hD₀ hDsmall hrlarge hGr hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.2.1
    (Real.log_pos (by linarith)) j hj hcnt.2.2 e e' hoff.1
    (hoff.2.1.trans (by have := Real.sqrt_nonneg (groupWidth p n j); linarith)) hoff.2.2.1 hoff.2.2.2
  have hchord : ∀ i : Fin (groupBlocks p n j+1), x+
      (groupTime p n q j i.val : ℝ)/(groupSamples p n q j : ℝ)*(x'-x)+
        W*Real.sqrt (groupSamples p n q j : ℝ) ≤ groupBarrier p n κ (gStar*ell n) q j i.val := by
    intro i
    have hh := actual_group_chord_bound p n κ (gStar*ell n) B₀ α
      (W*Real.sqrt (groupSamples p n q j : ℝ)) q hκp hα hgeom.1.le j hj hHp hcnt.2.1 e e'
      hmargin.1 hmargin.2 i.val (by omega)
    rwa [hxe, hxe'] at hh
  have hU : 0 ≤ groupU p n κ q j := le_trans (by norm_num) (groupU_controls_terms p n κ q hrpos j).1
  have hus := husmall κ η C_E q hreg j hj
  have hsmall : D*groupU p n κ q j ≤ δ*α*Real.sqrt (groupWidth p n j) := by
    have hh := mul_le_mul_of_nonneg_left hus hD.le
    have hid : D*(δ*α/D*Real.sqrt (groupWidth p n j))=δ*α*Real.sqrt (groupWidth p n j) := by field_simp
    rwa [hid] at hh
  have hmean := group_mean_deviation_small (groupSamples p n q j) (groupWidth p n j) α D
    (groupU p n κ q j) δ (x'-x) (deriv lambda (criticalPoint κ)) hQreal hHp hα hδ.le hcnt.2.1 hdrift hsmall
  have ht : ∀ i : Fin (groupBlocks p n j+1), groupTime p n q j i.val ≤ groupSamples p n q j-1+1 := by
    intro i
    rw [hQeq]
    exact groupTime_le_samples p n q j i.val hj (by omega)
  have hker := hkernel (criticalPoint κ) hs (groupSamples p n q j-1) hfree
    (Fin (groupBlocks p n j+1)) (fun i => groupTime p n q j i.val) ht
    (fun i => groupBarrier p n κ (gStar*ell n) q j i.val) x x'
    (by simpa only [hQeq] using hmean) (by simpa only [hQeq] using hchord)
  have hker' : cb/Real.sqrt (groupSamples p n q j : ℝ)*
      Real.exp (-K*((x'-x)-(groupSamples p n q j : ℝ)*deriv lambda (criticalPoint κ))^2/
        (groupSamples p n q j : ℝ)) ≤ actualCoarseKernel p n κ (gStar*ell n) q j x x' := by
    simpa only [hQeq, actualCoarseKernel] using hker
  exact (group_gaussian_kernel_scaling (groupSamples p n q j) (groupWidth p n j) α A D
    (groupU p n κ q j) cb K (x'-x) (deriv lambda (criticalPoint κ)) hQreal hHp hα hA
    hD.le hU hcb.le hK.le hcnt.2.1 hcnt.2.2 hdrift).trans hker'

#print axioms actual_regular_coarse_minorization

end ConditionalSpectralExtremes.CoarseBoxes
