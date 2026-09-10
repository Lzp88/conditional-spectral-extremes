import Mathlib
import BoxAlgebra

/-! A product of pointwise transition kernels integrated over a genuine
finite-dimensional chain of endpoint boxes. The lower bound integrates all
intermediate widths; it does not impose a narrow endpoint window on every
group. Identification with a particular random path is a separate theorem. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def endpointPath (n : ℕ) (x₀ : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons x₀ y

def boxChainIntegral (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (lo hi : Fin n → ℝ) (x₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : Fin n → ℝ, (Icc lo hi).indicator
    (fun y => ∏ i, K i (endpointPath n x₀ y i.castSucc) (y i)) y

theorem cons_mem_box {n : ℕ} (lo hi y : Fin n → ℝ) (x₀ : ℝ)
    (hy : y ∈ Icc lo hi) :
    endpointPath n x₀ y ∈ Icc (endpointPath n x₀ lo) (endpointPath n x₀ hi) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [endpointPath]
    · simpa [endpointPath] using hy.1 j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [endpointPath]
    · simpa [endpointPath] using hy.2 j

theorem boxChainIntegral_lower (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (lo hi : Fin n → ℝ) (x₀ : ℝ) (l : Fin n → ℝ≥0∞)
    (hK : ∀ i, ∀ x ∈ Icc (endpointPath n x₀ lo i.castSucc) (endpointPath n x₀ hi i.castSucc),
      ∀ x' ∈ Icc (lo i) (hi i), l i ≤ K i x x') :
    (∏ i, l i) * ∏ i, ENNReal.ofReal (hi i-lo i) ≤ boxChainIntegral n K lo hi x₀ := by
  have hconst : ∫⁻ y : Fin n → ℝ, (Icc lo hi).indicator (fun _ => ∏ i, l i) y =
      (∏ i, l i) * ∏ i, ENNReal.ofReal (hi i-lo i) := by
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc_pi]
  rw [← hconst]
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ Icc lo hi
  · simp only [Set.indicator_of_mem hy]
    apply Finset.prod_le_prod'
    intro i _
    have hc := cons_mem_box lo hi y x₀ hy
    exact hK i _ ⟨hc.1 i.castSucc, hc.2 i.castSucc⟩ _ ⟨hy.1 i, hy.2 i⟩
  · simp only [Set.indicator_of_notMem hy, le_refl]

theorem boxChainIntegral_real_lower (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (lo hi : Fin n → ℝ) (x₀ : ℝ) (l : Fin n → ℝ)
    (hlohi : lo ≤ hi) (hl : ∀ i, 0 ≤ l i)
    (hfinite : boxChainIntegral n K lo hi x₀ ≠ ⊤)
    (hK : ∀ i, ∀ x ∈ Icc (endpointPath n x₀ lo i.castSucc) (endpointPath n x₀ hi i.castSucc),
      ∀ x' ∈ Icc (lo i) (hi i), ENNReal.ofReal (l i) ≤ K i x x') :
    (∏ i, l i) * ∏ i, (hi i-lo i) ≤ (boxChainIntegral n K lo hi x₀).toReal := by
  have hh := ENNReal.toReal_mono hfinite
    (boxChainIntegral_lower n K lo hi x₀ (fun i => ENNReal.ofReal (l i)) hK)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_prod,
    ENNReal.toReal_ofReal (hl _), ENNReal.toReal_ofReal (sub_nonneg.mpr (hlohi _))] using hh

theorem product_gaussian_kernel_factors (n : ℕ) (c C : ℝ)
    (w U : Fin n → ℝ) :
    (∏ i, c / w i * Real.exp (-C*(U i)^2)) =
      c^n * (∏ i, (w i)⁻¹) * Real.exp (-C*(∑ i, (U i)^2)) := by
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, ← Finset.mul_sum]

#print axioms cons_mem_box
#print axioms boxChainIntegral_lower
#print axioms boxChainIntegral_real_lower
#print axioms product_gaussian_kernel_factors

end ConditionalSpectralExtremes
