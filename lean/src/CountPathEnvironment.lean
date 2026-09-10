import PoissonMaximumFourthMoment

/-! The literal maximum of centered count prefixes, with a deterministic
centering error bound relative to the actual Poisson means. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
open FiniteWalk

def countPathMaximum {q : ℕ} (μ : ℝ) (X : Fin q → ℕ) : ℝ :=
  (Finset.range (q+1)).sup' Finset.nonempty_range_add_one
    (fun j => |partialSum j (fun i => (X i : ℝ)-μ)|)

def countPathEnvironment {q : ℕ} (H μ : ℝ) (X : Fin q → ℕ) : ℝ :=
  1+countPathMaximum μ X/Real.sqrt H

theorem countPathMaximum_nonneg {q : ℕ} (μ : ℝ) (X : Fin q → ℕ) : 0 ≤ countPathMaximum μ X :=
  (abs_nonneg _).trans (Finset.le_sup' (fun j => |partialSum j (fun i => (X i : ℝ)-μ)|)
    (Finset.mem_range.mpr (Nat.succ_pos q)))

theorem countPathEnvironment_one_le {q : ℕ} (H μ : ℝ) (X : Fin q → ℕ) :
    1 ≤ countPathEnvironment H μ X := by
  unfold countPathEnvironment
  linarith [div_nonneg (countPathMaximum_nonneg μ X) (Real.sqrt_nonneg H)]

theorem countPathMaximum_poisson_drift {q : ℕ} (α : Fin q → ℝ≥0) (μ : ℝ) (X : Fin q → ℕ) :
    countPathMaximum μ X ≤ poissonPrefixMaximum α X+∑ i, |(α i : ℝ)-μ| := by
  have hp (j : ℕ) : |partialSum j (fun i => (X i : ℝ)-μ)| ≤
      |centeredPoissonPartial α j X|+∑ i, |(α i : ℝ)-μ| := by
    have he : partialSum j (fun i => (X i : ℝ)-μ) =
        centeredPoissonPartial α j X+∑ i ∈ prefixIndices q j, ((α i : ℝ)-μ) := by
      unfold centeredPoissonPartial centeredPoisson partialSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _))
  apply Finset.sup'_le
  intro j hj
  exact (hp j).trans (add_le_add (Finset.le_sup' (fun j => |centeredPoissonPartial α j X|) hj) le_rfl)

theorem countPathEnvironment_poisson_bound {q : ℕ} (α : Fin q → ℝ≥0) (H μ : ℝ)
    (hH : 0 < H) (hδ : (∑ i, |(α i : ℝ)-μ|) ≤ Real.sqrt H) (X : Fin q → ℕ) :
    countPathEnvironment H μ X ≤ 2+poissonPrefixMaximum α X/Real.sqrt H := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hb := div_le_div_of_nonneg_right
    ((countPathMaximum_poisson_drift α μ X).trans (add_le_add le_rfl hδ)) hs.le
  have he : (poissonPrefixMaximum α X+Real.sqrt H)/Real.sqrt H =
      poissonPrefixMaximum α X/Real.sqrt H+1 := by rw [add_div, div_self hs.ne']
  unfold countPathEnvironment
  rw [he] at hb
  linarith

theorem countPathEnvironment_fourth_bound {q : ℕ} (α : Fin q → ℝ≥0) (H μ : ℝ)
    (hH : 0 < H) (hδ : (∑ i, |(α i : ℝ)-μ|) ≤ Real.sqrt H) (X : Fin q → ℕ) :
    (countPathEnvironment H μ X)^4 ≤ 128+8*(poissonPrefixMaximum α X)^4/H^2 := by
  have hE : 0 ≤ countPathEnvironment H μ X := zero_le_one.trans (countPathEnvironment_one_le H μ X)
  have hM : 0 ≤ poissonPrefixMaximum α X/Real.sqrt H :=
    div_nonneg (poissonPrefixMaximum_nonneg α X) (Real.sqrt_nonneg H)
  have hb := (pow_le_pow_left₀ hE (countPathEnvironment_poisson_bound α H μ hH hδ X) 4).trans
    (add_pow_le (by norm_num : (0 : ℝ) ≤ 2) hM 4)
  have hs : Real.sqrt H ^ 4 = H^2 := by
    calc
      _ = (Real.sqrt H ^ 2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hH.le]
  norm_num only [Nat.reduceSub, show (2 : ℝ)^3 = 8 by norm_num,
    show (2 : ℝ)^4 = 16 by norm_num] at hb
  rw [div_pow, hs] at hb
  calc
    _ ≤ 8*(16+(poissonPrefixMaximum α X)^4/H^2) := hb
    _ = _ := by ring

#print axioms countPathMaximum_nonneg
#print axioms countPathEnvironment_one_le
#print axioms countPathMaximum_poisson_drift
#print axioms countPathEnvironment_poisson_bound
#print axioms countPathEnvironment_fourth_bound

end ConditionalSpectralExtremes.BlockCounts
