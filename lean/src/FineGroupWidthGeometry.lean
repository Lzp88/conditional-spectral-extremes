import FineScaleGeometry

/-! Pointwise widths of the actual computed group list: neighboring
ratios, exact first/last widths, and the total-width bound. -/

noncomputable section
namespace ConditionalSpectralExtremes.FineScales
open ConditionalSpectralAudit.DyadicGrouping

theorem groupWidth_adjacent (p : Parameters) (n j : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hj : j+1 < groupNumber p n) :
    groupWidth p n j ≤ 4*groupWidth p n (j+1) ∧
      groupWidth p n (j+1) ≤ 4*groupWidth p n j := by
  have hc := dyadic_groups_adjacent (count p n) (baseBlocks p n) hv hm
  rw [List.isChain_iff_getElem] at hc
  have hh := hc j hj
  have hj1 : j+1 < (groups p n).length := hj
  have hj0 : j < (groups p n).length := by omega
  dsimp [groupWidth, groupBlocks]
  rw [List.getElem?_eq_getElem hj0, List.getElem?_eq_getElem hj1]
  simp only [Option.getD_some]
  constructor
  · have hb : ((groups p n)[j] : ℝ) ≤ 4*((groups p n)[j+1] : ℝ) := by exact_mod_cast hh.1
    nlinarith [mul_le_mul_of_nonneg_right hb hω]
  · have hb : ((groups p n)[j+1] : ℝ) ≤ 4*((groups p n)[j] : ℝ) := by exact_mod_cast hh.2
    nlinarith [mul_le_mul_of_nonneg_right hb hω]

theorem sqrt_groupWidth_adjacent (p : Parameters) (n j : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hj : j+1 < groupNumber p n) :
    Real.sqrt (groupWidth p n j) ≤ 2*Real.sqrt (groupWidth p n (j+1)) ∧
      Real.sqrt (groupWidth p n (j+1)) ≤ 2*Real.sqrt (groupWidth p n j) := by
  have hh := groupWidth_adjacent p n j hv hm hω hj
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  constructor
  · have hb := Real.sqrt_le_sqrt hh.1
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4] using hb
  · have hb := Real.sqrt_le_sqrt hh.2
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4] using hb

theorem groupWidth_boundary_exact (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 6*baseBlocks p n ≤ count p n) :
    groupWidth p n 0 = (baseBlocks p n : ℝ)*omega p n ∧
      groupWidth p n (groupNumber p n-1) = (baseBlocks p n : ℝ)*omega p n := by
  have hh := dyadic_groups_boundary_exact (count p n) (baseBlocks p n) hv hm
  rw [List.head?_eq_getElem?] at hh
  rw [List.getLast?_eq_getElem?] at hh
  constructor
  · unfold groupWidth groupBlocks
    rw [show (groups p n)[0]?=some (baseBlocks p n) from hh.1]
    rfl
  · unfold groupWidth groupBlocks groupNumber
    rw [show (groups p n)[(groups p n).length-1]?=some (baseBlocks p n) from hh.2]
    rfl

theorem groupWidth_boundary_le_two_base (p : Parameters) (n : ℕ)
    (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hωb : omega p n ≤ baseWidth p n) (hm : 6*baseBlocks p n ≤ count p n) :
    groupWidth p n 0 ≤ 2*baseWidth p n ∧
      groupWidth p n (groupNumber p n-1) ≤ 2*baseWidth p n := by
  have hh := groupWidth_boundary_exact p n (baseBlocks_pos p n hω hb) hm
  have hr := (baseBlocks_width_bounds p n hω hb.le).2
  rw [hh.1, hh.2]
  constructor <;> linarith

theorem groupWidth_le_distance (p : Parameters) (n j : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hj : j < groupNumber p n) :
    groupWidth p n j ≤ aStar n-r p n := by
  have hstart := groupStart_le_count p n (j+1) hv hm
  rw [group_start_step p n j hj] at hstart
  have hb : groupBlocks p n j ≤ count p n := by omega
  have hcount : (count p n : ℝ) ≠ 0 := by exact_mod_cast (show count p n ≠ 0 by omega)
  have hdist : (count p n : ℝ)*omega p n=aStar n-r p n := by
    unfold omega
    field_simp [hcount]
  rw [← hdist]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hω

#print axioms groupWidth_adjacent
#print axioms sqrt_groupWidth_adjacent
#print axioms groupWidth_boundary_exact
#print axioms groupWidth_boundary_le_two_base
#print axioms groupWidth_le_distance

end ConditionalSpectralExtremes.FineScales
