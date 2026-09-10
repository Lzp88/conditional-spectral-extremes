import CountPathEnvironment
import CountCouplingKernel
import MultinomialSubsetMoments

/-! Deterministic control of all count-path environments by the single
discrepancy vector of the actual coupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open FiniteWalk

theorem countPathMaximum_comparison {q : ℕ} (μ : ℝ) (X Y : Fin q → ℕ) :
    countPathMaximum μ X ≤ countPathMaximum μ Y+∑ i, |(X i : ℝ)-(Y i : ℝ)| := by
  have hp (j : ℕ) : |partialSum j (fun i => (X i : ℝ)-μ)| ≤
      |partialSum j (fun i => (Y i : ℝ)-μ)|+∑ i, |(X i : ℝ)-(Y i : ℝ)| := by
    have he : partialSum j (fun i => (X i : ℝ)-μ) =
        partialSum j (fun i => (Y i : ℝ)-μ)+∑ i ∈ prefixIndices q j, ((X i : ℝ)-(Y i : ℝ)) := by
      unfold partialSum
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
  exact (hp j).trans (add_le_add
    (Finset.le_sup' (fun j => |partialSum j (fun i => (Y i : ℝ)-μ)|) hj) le_rfl)

theorem countPathMaximum_lipschitz {q : ℕ} (μ : ℝ) (X Y : Fin q → ℕ) :
    |countPathMaximum μ X-countPathMaximum μ Y| ≤ ∑ i, |(X i : ℝ)-(Y i : ℝ)| := by
  have hXY := countPathMaximum_comparison μ X Y
  have hYX := countPathMaximum_comparison μ Y X
  have hs : (∑ i, |(Y i : ℝ)-(X i : ℝ)|) = ∑ i, |(X i : ℝ)-(Y i : ℝ)| :=
    Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
  rw [hs] at hYX
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

theorem countPathEnvironment_coupled {ι : Type*} [Fintype ι] {q : ℕ}
    (e : Fin q ↪ ι) (H μ : ℝ) (hH : 0 < H) (z : CoupledCounts ι) (hz : CountsCoupled z) :
    |countPathEnvironment H μ (fun i => z.1 (e i))-
      countPathEnvironment H μ (fun i => z.2.1 (e i))| ≤
        subsetCount (Finset.univ.map e) z.2.2/Real.sqrt H := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hcount (i : Fin q) : |(z.1 (e i) : ℝ)-(z.2.1 (e i) : ℝ)| = (z.2.2 (e i) : ℝ) := by
    simpa only [Finset.sum_singleton] using CountsCoupled_all_partial_sums hz {e i}
  have hh := countPathMaximum_lipschitz μ (fun i => z.1 (e i)) (fun i => z.2.1 (e i))
  simp only [hcount] at hh
  have he : subsetCount (Finset.univ.map e) z.2.2 = ∑ i, (z.2.2 (e i) : ℝ) := by
    unfold subsetCount
    rw [Finset.sum_map]
  rw [he]
  have he' : countPathEnvironment H μ (fun i => z.1 (e i))-
      countPathEnvironment H μ (fun i => z.2.1 (e i)) =
        (countPathMaximum μ (fun i => z.1 (e i))-countPathMaximum μ (fun i => z.2.1 (e i)))/Real.sqrt H := by
    unfold countPathEnvironment
    ring
  rw [he', abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right hh hs.le

theorem countPathEnvironment_coupled_square {ι : Type*} [Fintype ι] {q : ℕ}
    (e : Fin q ↪ ι) (H μ : ℝ) (hH : 0 < H) (z : CoupledCounts ι) (hz : CountsCoupled z) :
    (countPathEnvironment H μ (fun i => z.1 (e i))-
      countPathEnvironment H μ (fun i => z.2.1 (e i)))^2 ≤
        (subsetCount (Finset.univ.map e) z.2.2)^2/H := by
  have hh := pow_le_pow_left₀ (abs_nonneg _)
    (countPathEnvironment_coupled e H μ hH z hz) 2
  rw [sq_abs, div_pow, Real.sq_sqrt hH.le] at hh
  exact hh

#print axioms countPathMaximum_comparison
#print axioms countPathMaximum_lipschitz
#print axioms countPathEnvironment_coupled
#print axioms countPathEnvironment_coupled_square

end ConditionalSpectralExtremes.BlockCounts
