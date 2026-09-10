import HarmonicFiniteIntervals
import FineBlockCategories

/-! Literal harmonic masses of the manuscript's fine exponential blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

def fineCategoryBlock (p : Parameters) (n : ℕ) : ShortIndex n (cutoff n) → Fin (count p n+1) :=
  fun j => category p n (j.val.val+1)

def fineHarmonicMass (p : Parameters) (n : ℕ) (i : Fin (count p n+1)) : ℝ :=
  shortBlockHarmonicMass n (cutoff n) (fineCategoryBlock p n) i

theorem coordinate_mono (p : Parameters) (n : ℕ) (hω : 0 ≤ omega p n) :
    Monotone (coordinate p n) := by
  intro i j hij
  unfold coordinate
  have hh : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hω)

theorem exp_coordinate_le_cutoff (p : Parameters) (n i : ℕ)
    (hω : 0 ≤ omega p n) (hc : 0 < count p n) (hcut : 0 < cutoff n) (hi : i ≤ count p n) :
    Real.exp (coordinate p n i) ≤ cutoff n := by
  have hh := coordinate_mono p n hω hi
  rw [coordinate_last p n hc] at hh
  calc
    _ ≤ Real.exp (aStar n) := Real.exp_le_exp.mpr hh
    _ = _ := Real.exp_log (by exact_mod_cast hcut)

theorem fineHarmonicMass_exact (p : Parameters) (n : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n) (hcut : 0 < cutoff n) (hcn : cutoff n ≤ n)
    (i : Fin (count p n+1)) (hi : 0 < i.val) :
    fineHarmonicMass p n i = harmonicNumber ⌊Real.exp (coordinate p n i.val)⌋₊-
      harmonicNumber ⌊Real.exp (coordinate p n (i.val-1))⌋₊ := by
  apply shortBlockHarmonicMass_interval n (cutoff n) hcn (fineCategoryBlock p n) i
    (Real.exp (coordinate p n (i.val-1))) (Real.exp (coordinate p n i.val))
    (Real.exp_le_exp.mpr (coordinate_mono p n hω.le (Nat.sub_le _ _)))
    (exp_coordinate_le_cutoff p n i.val hω.le hc hcut (by omega))
  intro j
  change category p n (j.val.val+1) = i ↔ _
  rw [Fin.ext_iff]
  exact category_positive_iff p n (j.val.val+1) i.val hω hc (by omega) j.property hi

theorem fineHarmonicMass_error (p : Parameters) (n : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n) (hcut : 0 < cutoff n) (hcn : cutoff n ≤ n)
    (hr : Real.log 2 ≤ r p n) (i : Fin (count p n+1)) (hi : 0 < i.val) :
    |fineHarmonicMass p n i-omega p n| ≤ 4*Real.exp (-coordinate p n (i.val-1)) := by
  have hcoords : coordinate p n i.val-coordinate p n (i.val-1) = omega p n := by
    unfold coordinate
    rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one]
    ring
  have hstart : Real.log 2 ≤ coordinate p n (i.val-1) := by
    have hh := coordinate_mono p n hω.le (Nat.zero_le (i.val-1))
    rw [coordinate_zero] at hh
    exact hr.trans hh
  have hh := harmonic_exponential_interval_error (coordinate p n (i.val-1))
    (coordinate p n i.val) hstart (coordinate_mono p n hω.le (Nat.sub_le _ _))
  rw [fineHarmonicMass_exact p n hω hc hcut hcn i hi]
  simpa only [hcoords] using hh

theorem fineHarmonicMass_initial (p : Parameters) (n : ℕ)
    (hω : 0 < omega p n) (hc : 0 < count p n) (hcut : 0 < cutoff n) (hcn : cutoff n ≤ n) :
    fineHarmonicMass p n 0 = harmonicNumber ⌊Real.exp (r p n)⌋₊ := by
  have hupper : Real.exp (r p n) ≤ cutoff n := by
    simpa only [coordinate_zero] using exp_coordinate_le_cutoff p n 0 hω.le hc hcut (Nat.zero_le _)
  have hh := shortBlockHarmonicMass_interval n (cutoff n) hcn (fineCategoryBlock p n) 0
    0 (Real.exp (r p n)) (Real.exp_nonneg _) hupper (by
      intro j
      change category p n (j.val.val+1) = 0 ↔ _
      rw [Fin.ext_iff]
      have hp : (0 : ℝ) < ((j.val.val+1 : ℕ) : ℝ) := by positivity
      simp only [Fin.val_zero, hp, true_and]
      exact category_zero_iff p n (j.val.val+1) hω hc (by omega) j.property)
  simpa only [fineHarmonicMass, Nat.floor_zero, harmonicNumber, Finset.range_zero,
    Finset.sum_empty, sub_zero] using hh

#print axioms coordinate_mono
#print axioms exp_coordinate_le_cutoff
#print axioms fineHarmonicMass_exact
#print axioms fineHarmonicMass_error
#print axioms fineHarmonicMass_initial

end ConditionalSpectralExtremes.BlockCounts
