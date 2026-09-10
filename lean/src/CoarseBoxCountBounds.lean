import CoarseBoxDefinitions

/-! Exact coarse count discrepancies and count/width comparison from the
regular environment. The final comparison does not depend on eta. -/

noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem groupSamples_discrepancy (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (hj : j < groupNumber p n) (hH : 0 < groupWidth p n j) :
    |(groupSamples p n q j : ℝ)-κ*groupWidth p n j| ≤
      environmentE p n κ q j*Real.sqrt (groupWidth p n j) := by
  have hh := localDiscrepancy_bound (omega p n) κ q (groupStart p n j)
    (groupBlocks p n j) (groupBlocks p n j) hH le_rfl
  rw [groupSamples_cast p n q j hj, group_start_step p n j hj]
  simpa only [localDiscrepancy, environmentE, groupWidth, mul_assoc] using! hh

theorem groupSamples_comparable (p : Parameters) (n : ℕ) (κ κmin κmax : ℝ)
    (q : ℕ → ℕ) (j : ℕ) (hj : j < groupNumber p n)
    (hH : 0 < groupWidth p n j) (hκmin : 0 < κmin)
    (hκ : κ ∈ Set.Icc κmin κmax)
    (hsmall : environmentE p n κ q j ≤ κmin/2*Real.sqrt (groupWidth p n j)) :
    κmin/2*groupWidth p n j ≤ (groupSamples p n q j : ℝ) ∧
      (groupSamples p n q j : ℝ) ≤ 2*κmax*groupWidth p n j := by
  have hd := groupSamples_discrepancy p n κ q j hj hH
  have hh := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg (groupWidth p n j))
  have hsq := Real.sq_sqrt hH.le
  have hlo := (abs_le.mp hd).1
  have hhi := (abs_le.mp hd).2
  have hκlo := mul_le_mul_of_nonneg_right hκ.1 hH.le
  have hκhi := mul_le_mul_of_nonneg_right hκ.2 hH.le
  have hκorder := hκ.1.trans hκ.2
  have hprod := mul_le_mul_of_nonneg_right hκorder hH.le
  constructor <;> nlinarith

theorem regular_groupSamples_comparable (p : Parameters) (n : ℕ)
    (κ κmin κmax η K_E C_E : ℝ) (q : ℕ → ℕ)
    (hreg : Regular p n κ η K_E C_E q)
    (hκmin : 0 < κmin) (hκ : κ ∈ Set.Icc κmin κmax)
    (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hm : 2*baseBlocks p n ≤ count p n)
    (hsmall : K_E*Real.sqrt (Real.log (ReservoirScale.ell n)) ≤
      κmin/2*Real.sqrt (baseWidth p n))
    (j : ℕ) (hj : j < groupNumber p n) :
    κmin/2*groupWidth p n j ≤ (groupSamples p n q j : ℝ) ∧
      (groupSamples p n q j : ℝ) ≤ 2*κmax*groupWidth p n j := by
  have hH := groupWidth_ge_base p n j hω hb hm hj
  apply groupSamples_comparable p n κ κmin κmax q j hj (hb.trans_le hH) hκmin hκ
  exact (hreg.2.1 j (Finset.mem_range.mpr hj)).trans
    (hsmall.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) (by positivity)))

#print axioms groupSamples_discrepancy
#print axioms groupSamples_comparable
#print axioms regular_groupSamples_comparable

end ConditionalSpectralExtremes.CoarseBoxes
