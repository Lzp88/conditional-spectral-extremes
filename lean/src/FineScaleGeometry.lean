import FineScaleDefinitions

/-! Deterministic bounds for the literal fine and coarse scales. The
rounding errors and grouping invariants are proved from their definitions. -/

noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes.FineScales
open ConditionalSpectralAudit.DyadicGrouping

theorem count_pos (p : Parameters) (n : ℕ) (hh : 0 < h p n)
    (hd : 0 < aStar n-r p n) : 0 < count p n := by
  exact Nat.one_le_ceil_iff.mpr (div_pos hd hh)

theorem omega_bounds (p : Parameters) (n : ℕ) (hh : 0 < h p n)
    (hd : h p n ≤ aStar n-r p n) : h p n/2 ≤ omega p n ∧ omega p n ≤ h p n := by
  have hdist : 0 < aStar n-r p n := hh.trans_le hd
  have hm : 0 < (count p n : ℝ) := Nat.cast_pos.mpr (count_pos p n hh hdist)
  have hceil := Nat.le_ceil ((aStar n-r p n)/h p n)
  have hceil' := Nat.ceil_lt_add_one (div_nonneg hdist.le hh.le)
  change (aStar n-r p n)/h p n ≤ (count p n : ℝ) at hceil
  change (count p n : ℝ) < (aStar n-r p n)/h p n+1 at hceil'
  have hlo := (div_le_iff₀ hh).1 hceil
  have hhi : (count p n : ℝ)*h p n < aStar n-r p n+h p n := by
    have ht := mul_lt_mul_of_pos_right hceil' hh
    field_simp at ht
    nlinarith
  unfold omega
  constructor
  · apply (le_div_iff₀ hm).2
    nlinarith
  · exact (div_le_iff₀ hm).2 (by nlinarith)

theorem baseBlocks_pos (p : Parameters) (n : ℕ) (hω : 0 < omega p n)
    (hb : 0 < baseWidth p n) : 0 < baseBlocks p n := by
  exact Nat.one_le_ceil_iff.mpr (div_pos hb hω)

theorem baseBlocks_width_bounds (p : Parameters) (n : ℕ) (hω : 0 < omega p n)
    (hb : 0 ≤ baseWidth p n) :
    baseWidth p n ≤ (baseBlocks p n : ℝ)*omega p n ∧
      (baseBlocks p n : ℝ)*omega p n < baseWidth p n+omega p n := by
  have hl := Nat.le_ceil (baseWidth p n/omega p n)
  have hu := Nat.ceil_lt_add_one (div_nonneg hb hω.le)
  change baseWidth p n/omega p n ≤ (baseBlocks p n : ℝ) at hl
  change (baseBlocks p n : ℝ) < baseWidth p n/omega p n+1 at hu
  constructor
  · exact (div_le_iff₀ hω).1 hl
  · have hh := mul_lt_mul_of_pos_right hu hω
    field_simp at hh
    nlinarith

theorem groups_sum (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    (groups p n).sum = count p n := (dyadic_groups_invariants _ _ hv hm).1

theorem groupStart_le_count (p : Parameters) (n j : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    groupStart p n j ≤ count p n := by
  have hh := congrArg List.sum (List.take_append_drop j (groups p n))
  rw [List.sum_append, groups_sum p n hv hm] at hh
  change groupStart p n j+(List.drop j (groups p n)).sum=count p n at hh
  omega

theorem groupStart_last (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    groupStart p n (groupNumber p n) = count p n := by
  simpa only [groupStart, groupNumber, List.take_length] using groups_sum p n hv hm

theorem groupWidth_ge_base (p : Parameters) (n j : ℕ)
    (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hm : 2*baseBlocks p n ≤ count p n) (hj : j < groupNumber p n) :
    baseWidth p n ≤ groupWidth p n j := by
  have hv := baseBlocks_pos p n hω hb
  have hj' : j < (groups p n).length := hj
  have hg : (groups p n)[j] ∈ groups p n := List.getElem_mem hj'
  have hmin := (dyadic_groups_invariants _ _ hv hm).2 _ hg
  have hbnd := (baseBlocks_width_bounds p n hω hb.le).1
  unfold groupWidth groupBlocks
  rw [List.getElem?_eq_getElem hj', Option.getD_some]
  exact hbnd.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) hω.le)

theorem countPrefix_add (q : ℕ → ℕ) (start width : ℕ) :
    countPrefix q (start+width) = countPrefix q start+
      ∑ j ∈ Finset.range width, q (start+j+1) := by
  exact Finset.sum_range_add (fun j => q (j+1)) start width

theorem countPrefix_difference (q : ℕ → ℕ) (start width : ℕ) :
    (countPrefix q (start+width) : ℝ)-(countPrefix q start : ℝ) =
      ∑ j ∈ Finset.range width, (q (start+j+1) : ℝ) := by
  rw [countPrefix_add, Nat.cast_add, Nat.cast_sum]
  ring

theorem fine_count_bounds_to_group (p : Parameters) (n : ℕ) (κ η : ℝ) (q : ℕ → ℕ)
    (hcounts : ∀ i ∈ Finset.range (count p n), κ/2*omega p n ≤ (q (i+1) : ℝ) ∧
      (q (i+1) : ℝ) ≤ (κ+η)*omega p n)
    (start width : ℕ) (hrange : start+width ≤ count p n) :
    κ/2*((width : ℝ)*omega p n) ≤
        (countPrefix q (start+width) : ℝ)-countPrefix q start ∧
      (countPrefix q (start+width) : ℝ)-countPrefix q start ≤
        (κ+η)*((width : ℝ)*omega p n) := by
  rw [countPrefix_difference]
  have hl := Finset.sum_le_sum (s := Finset.range width)
    (fun j hj => (hcounts (start+j) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))).1)
  have hu := Finset.sum_le_sum (s := Finset.range width)
    (fun j hj => (hcounts (start+j) (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))).2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hl hu
  constructor <;> nlinarith

theorem regular_group_count_bounds (p : Parameters) (n : ℕ) (κ η K_E C_E : ℝ) (q : ℕ → ℕ)
    (hreg : Regular p n κ η K_E C_E q)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : ℕ) (hj : j < groupNumber p n) :
    κ/2*groupWidth p n j ≤
        (countPrefix q (groupStart p n (j+1)) : ℝ)-countPrefix q (groupStart p n j) ∧
      (countPrefix q (groupStart p n (j+1)) : ℝ)-countPrefix q (groupStart p n j) ≤
        (κ+η)*groupWidth p n j := by
  have hg := groupStart_le_count p n (j+1) hv hm
  rw [group_start_step p n j hj] at hg ⊢
  exact fine_count_bounds_to_group p n κ η q hreg.1 _ _ hg

#print axioms count_pos
#print axioms omega_bounds
#print axioms baseBlocks_pos
#print axioms baseBlocks_width_bounds
#print axioms groups_sum
#print axioms groupStart_le_count
#print axioms groupStart_last
#print axioms groupWidth_ge_base
#print axioms countPrefix_add
#print axioms countPrefix_difference
#print axioms fine_count_bounds_to_group
#print axioms regular_group_count_bounds

end ConditionalSpectralExtremes.FineScales
