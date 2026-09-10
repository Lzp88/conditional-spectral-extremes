import CoarseCountCoordinates
import FineHarmonicAsymptotics

/-! Exact harmonic masses of the literal coarse blocks, including the
global cumulative error bound and the sum of their spatial widths. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales IIDRegroup

def coarseFineIndex (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) : Fin (groupBlocks p n j) ↪ Fin (count p n) where
  toFun i := ⟨groupStart p n j+i.val, by
    have hg := groupStart_le_count p n (j.val+1) hv hm
    rw [group_start_step p n j j.isLt] at hg
    have hi := i.isLt
    omega⟩
  inj' := by
    intro i l h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp only at hh
    omega

theorem coarseCountIndex_eq_some (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) (i : Fin (groupBlocks p n j)) :
    coarseCountIndex p n hv hm j i = some (coarseFineIndex p n hv hm j i).succ := rfl

def coarseHarmonicMass (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) : ℝ :=
  ∑ i, fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ

theorem coarseHarmonicMass_relative (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (δ : ℝ) (hδ : ∀ i : Fin (count p n+1), 0 < i.val →
      |fineHarmonicMass p n i-omega p n| ≤ δ*omega p n)
    (j : Fin (groupNumber p n)) :
    |coarseHarmonicMass p n hv hm j-groupWidth p n j| ≤ δ*groupWidth p n j := by
  have he : coarseHarmonicMass p n hv hm j-groupWidth p n j =
      ∑ i : Fin (groupBlocks p n j),
        (fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ-omega p n) := by
    rw [Finset.sum_sub_distrib]
    simp only [coarseHarmonicMass, groupWidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hδ (coarseFineIndex p n hv hm j i).succ (Nat.succ_pos _))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  unfold groupWidth
  nlinarith

theorem coarseHarmonicMass_error_sum_le (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) :
    (∑ i : Fin (groupBlocks p n j),
      |fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ-omega p n|) ≤
      ∑ i : Fin (count p n), |fineHarmonicMass p n i.succ-omega p n| := by
  have he : (∑ i : Fin (groupBlocks p n j),
      |fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ-omega p n|) =
      ∑ i ∈ Finset.univ.map (coarseFineIndex p n hv hm j),
        |fineHarmonicMass p n i.succ-omega p n| := by rw [Finset.sum_map]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)

theorem coarseHarmonicMass_scaled_error (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) (κ : ℝ) (hκ : 0 ≤ κ) :
    (∑ i : Fin (groupBlocks p n j),
      |κ*fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ-κ*omega p n|) ≤
      κ*∑ i : Fin (count p n), |fineHarmonicMass p n i.succ-omega p n| := by
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hκ]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (coarseHarmonicMass_error_sum_le p n hv hm j) hκ

theorem coarse_groupWidth_sum (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    (∑ j : Fin (groupNumber p n), groupWidth p n j) = aStar n-r p n := by
  have hsum : (∑ j : Fin (groupNumber p n), groupBlocks p n j) = count p n := by
    rw [Fin.sum_univ_eq_sum_range]
    change blockPrefix (groupBlocks p n) (groupNumber p n) = count p n
    rw [groupBlocks_prefix p n _ le_rfl, groupStart_last p n hv hm]
  have hc : (count p n : ℝ) ≠ 0 := by exact_mod_cast (show count p n ≠ 0 by omega)
  calc
    _ = (∑ j : Fin (groupNumber p n), (groupBlocks p n j : ℝ))*omega p n := by
      simp only [groupWidth, Finset.sum_mul]
    _ = (count p n : ℝ)*omega p n := by rw [← Nat.cast_sum, hsum]
    _ = _ := by unfold omega; field_simp

#print axioms coarseFineIndex
#print axioms coarseCountIndex_eq_some
#print axioms coarseHarmonicMass_relative
#print axioms coarseHarmonicMass_error_sum_le
#print axioms coarseHarmonicMass_scaled_error
#print axioms coarse_groupWidth_sum

end ConditionalSpectralExtremes.BlockCounts
