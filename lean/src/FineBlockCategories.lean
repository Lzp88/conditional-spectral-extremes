import FineScaleDefinitions

/-! The actual finite category map agrees exactly with the manuscript's
exponential half-open integer blocks, including all integer endpoints. -/

noncomputable section
namespace ConditionalSpectralExtremes.FineScales

theorem category_unclipped (p : Parameters) (n length : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n)
    (hlen : 0 < length) (hcut : length ≤ ReservoirScale.cutoff n) :
    (category p n length).val = ⌈(Real.log length-r p n)/omega p n⌉₊ := by
  have hlen' : (0 : ℝ) < length := Nat.cast_pos.mpr hlen
  have hlog : Real.log length ≤ aStar n :=
    Real.log_le_log hlen' (by exact_mod_cast hcut)
  have hlast := coordinate_last p n hc
  have hceil : ⌈(Real.log length-r p n)/omega p n⌉₊ ≤ count p n := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hω).2
    unfold coordinate at hlast
    linarith
  exact Nat.min_eq_right hceil

theorem category_zero_iff (p : Parameters) (n length : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n)
    (hlen : 0 < length) (hcut : length ≤ ReservoirScale.cutoff n) :
    (category p n length).val = 0 ↔ (length : ℝ) ≤ Real.exp (r p n) := by
  rw [category_unclipped p n length hω hc hlen hcut, Nat.ceil_eq_zero,
    div_le_iff₀ hω, zero_mul, sub_nonpos,
    Real.log_le_iff_le_exp (Nat.cast_pos.mpr hlen)]

theorem category_positive_iff (p : Parameters) (n length i : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n)
    (hlen : 0 < length) (hcut : length ≤ ReservoirScale.cutoff n) (hi : 0 < i) :
    (category p n length).val = i ↔
      Real.exp (coordinate p n (i-1)) < (length : ℝ) ∧
        (length : ℝ) ≤ Real.exp (coordinate p n i) := by
  rw [category_unclipped p n length hω hc hlen hcut, Nat.ceil_eq_iff hi.ne',
    lt_div_iff₀ hω, div_le_iff₀ hω,
    ← Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hlen),
    ← Real.log_le_iff_le_exp (Nat.cast_pos.mpr hlen)]
  unfold coordinate
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

#print axioms category_unclipped
#print axioms category_zero_iff
#print axioms category_positive_iff

end ConditionalSpectralExtremes.FineScales
