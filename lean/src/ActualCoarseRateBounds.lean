import FinePoissonRates
import CoarseScaleAsymptotics
import ReservoirShiftUniform

/-! The literal fine/coarse scales satisfy every rate and drift hypothesis
of the finite Poisson environment estimates, uniformly in k/log n on a
fixed positive compact interval. No rate approximation is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators NNReal Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale FineScales

theorem fine_omega_tendsto_atTop (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar) :
    Tendsto (omega p) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  filter_upwards [eventually_fine_scale_geometry p hA hr,
    (h_tendsto_atTop p hA).eventually_ge_atTop (2*R)] with n hf hh
  have hl := hf.2.2.2.2.1
  change 2*R ≤ p.A₀*ell n at hh
  linarith

theorem coarseWidth_eventually_ge (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar)
    (hD : 0 < p.D₀) (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (groupNumber p n), R ≤ groupWidth p n j := by
  filter_upwards [eventually_coarse_scale_geometry p hA hr hD,
    (fine_omega_tendsto_atTop p hA hr).eventually_ge_atTop R] with n hg hω
  intro j
  have hm : 2*baseBlocks p n ≤ count p n := by have := hg.2.2.2.2.1; omega
  exact hω.trans (hg.2.2.1.trans (groupWidth_ge_base p n j hg.1 hg.2.1 hm j.isLt))

structure CoarseRateBounds (p : Parameters) (n : ℕ) (a B : ℝ) : Prop where
  Lpos : 0 < L n
  probNonneg : ∀ i, 0 ≤ fineReferenceProbabilities p n i
  probSum : (∑ i, fineReferenceProbabilities p n i) = 1
  basePos : 0 < baseBlocks p n
  enoughBlocks : 2*baseBlocks p n ≤ count p n
  widthOne : ∀ j : Fin (groupNumber p n), 1 ≤ groupWidth p n j
  totalWidth : (∑ j : Fin (groupNumber p n), groupWidth p n j) ≤ L n
  massBound : ∀ j : Fin (groupNumber p n),
    (∑ i ∈ coarseCountSet p n basePos enoughBlocks j, fineReferenceProbabilities p n i) ≤ 2*groupWidth p n j/L n
  rateBounds : ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B → ∀ j : Fin (groupNumber p n),
    (1 ≤ ∑ i, (finePoissonRates p n k probNonneg (coarseCountIndex p n basePos enoughBlocks j i) : ℝ)) ∧
    ((∑ i, (finePoissonRates p n k probNonneg (coarseCountIndex p n basePos enoughBlocks j i) : ℝ)) ≤
      (2*B)*groupWidth p n j) ∧
    ((∑ i, |(finePoissonRates p n k probNonneg (coarseCountIndex p n basePos enoughBlocks j i) : ℝ)-
      ((k : ℝ)/L n)*omega p n|) ≤ Real.sqrt (groupWidth p n j))

theorem eventually_CoarseRateBounds (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar)
    (hD : 0 < p.D₀) {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∀ᶠ n : ℕ in atTop, CoarseRateBounds p n a B := by
  have hB : 0 < B := ha.trans_le haB
  have hErr := (fineHarmonicMass_total_error_tendsto_zero p hA hr).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/B))
  filter_upwards [eventually_coarse_scale_geometry p hA hr hD,
    coarseWidth_eventually_ge p hA hr hD (max 1 (2/a)),
    eventually_fineHarmonicMass_relative p hA hr (1/2) (by norm_num), hErr,
    L_tendsto_atTop.eventually_gt_atTop 0, T_tendsto_atTop.eventually_gt_atTop 0,
    cutoff_tendsto_atTop.eventually_ge_atTop 1, eventually_four_cutoff_le_n,
    (r_tendsto_atTop p hr).eventually_ge_atTop 0]
      with n hg hW hRel hE hL hT hcut hcutn hrn
  have hv : 0 < baseBlocks p n := hg.2.2.2.1
  have hm : 2*baseBlocks p n ≤ count p n := by have := hg.2.2.2.2.1; omega
  have hbn : cutoff n ≤ n := by omega
  have hp := (fineReferenceProbabilities_valid p n hL hT.le hbn).1
  have hs := (fineReferenceProbabilities_valid p n hL hT.le hbn).2
  have hH (j : Fin (groupNumber p n)) : 1 ≤ groupWidth p n j := (le_max_left _ _).trans (hW j)
  have htotal : (∑ j : Fin (groupNumber p n), groupWidth p n j) ≤ L n := by
    rw [coarse_groupWidth_sum p n hv hm]
    have hlog := Real.log_le_log (by exact_mod_cast (show 0 < cutoff n by omega) : (0 : ℝ) < cutoff n)
      (by exact_mod_cast hbn : (cutoff n : ℝ) ≤ n)
    change aStar n ≤ L n at hlog
    linarith
  have hmass (j : Fin (groupNumber p n)) :
      groupWidth p n j/2 ≤ coarseHarmonicMass p n hv hm j ∧
        coarseHarmonicMass p n hv hm j ≤ 2*groupWidth p n j := by
    have hh := abs_le.mp (coarseHarmonicMass_relative p n hv hm (1/2) hRel j)
    constructor <;> linarith [hH j]
  refine ⟨hL, hp, hs, hv, hm, hH, htotal, ?_, ?_⟩
  · intro j
    rw [fineReference_coarse_mass]
    exact div_le_div_of_nonneg_right (hmass j).2 hL.le
  · intro k hak hkB j
    have hκ : 0 ≤ (k : ℝ)/L n := ha.le.trans hak
    refine ⟨?_, ?_, ?_⟩
    · rw [finePoissonRates_coarse_sum]
      have hWa : 2/a ≤ groupWidth p n j := (le_max_right _ _).trans (hW j)
      have hprod := (div_le_iff₀ ha).mp hWa
      have h1 := mul_le_mul_of_nonneg_left (hmass j).1 hκ
      have h2 := mul_le_mul_of_nonneg_right hak (by linarith [hH j] : 0 ≤ groupWidth p n j/2)
      nlinarith
    · rw [finePoissonRates_coarse_sum]
      calc
        _ ≤ ((k : ℝ)/L n)*(2*groupWidth p n j) := mul_le_mul_of_nonneg_left (hmass j).2 hκ
        _ ≤ B*(2*groupWidth p n j) := mul_le_mul_of_nonneg_right hkB (by linarith [hH j])
        _ = _ := by ring
    · simp_rw [finePoissonRates_coarse]
      apply (coarseHarmonicMass_scaled_error p n hv hm j ((k : ℝ)/L n) hκ).trans
      have hEn : 0 ≤ ∑ i : Fin (count p n), |fineHarmonicMass p n i.succ-omega p n| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      change (∑ i : Fin (count p n), |fineHarmonicMass p n i.succ-omega p n|) < 1/B at hE
      have hEB := (le_div_iff₀ hB).mp hE.le
      calc
        _ ≤ B*∑ i : Fin (count p n), |fineHarmonicMass p n i.succ-omega p n| :=
          mul_le_mul_of_nonneg_right hkB hEn
        _ ≤ 1 := by nlinarith
        _ ≤ Real.sqrt (groupWidth p n j) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hH j)

#print axioms fine_omega_tendsto_atTop
#print axioms coarseWidth_eventually_ge
#print axioms eventually_CoarseRateBounds

end ConditionalSpectralExtremes.BlockCounts
