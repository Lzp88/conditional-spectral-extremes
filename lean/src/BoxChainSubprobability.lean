import BoxChainIntegral
import BridgeReversal

/-! Genuine finite-dimensional recursion and finiteness of the endpoint
box-chain integral for measurable subprobability transition densities. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem cons_mem_box_iff {n : ℕ} (lo hi : Fin (n+1) → ℝ) (a : ℝ) (y : Fin n → ℝ) :
    (Fin.cons a y : Fin (n+1) → ℝ) ∈ Icc lo hi ↔
      a ∈ Icc (lo 0) (hi 0) ∧ y ∈ Icc (Fin.tail lo) (Fin.tail hi) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa using h.1 0
    · simpa using h.2 0
    · intro i
      simpa only [Fin.cons_succ, Fin.tail] using! h.1 i.succ
    · intro i
      simpa only [Fin.cons_succ, Fin.tail] using! h.2 i.succ
  · rintro ⟨ha, hy⟩
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha.1
      · simpa only [Fin.cons_succ, Fin.tail] using! hy.1 j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha.2
      · simpa only [Fin.cons_succ, Fin.tail] using! hy.2 j

theorem endpointPath_cons_tail (n : ℕ) (x₀ a : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    endpointPath (n+1) x₀ (Fin.cons a y) i.succ.castSucc =
      endpointPath n a y i.castSucc := by
  change endpointPath (n+1) x₀ (endpointPath n a y) i.castSucc.succ = endpointPath n a y i.castSucc
  unfold endpointPath
  rw [Fin.cons_succ]

theorem endpoint_kernel_product_cons (n : ℕ) (K : Fin (n+1) → ℝ → ℝ → ℝ≥0∞)
    (x₀ a : ℝ) (y : Fin n → ℝ) :
    (∏ i, K i (endpointPath (n+1) x₀ (Fin.cons a y) i.castSucc) ((Fin.cons a y : Fin (n+1) → ℝ) i)) =
      K 0 x₀ a * ∏ i : Fin n, K i.succ (endpointPath n a y i.castSucc) (y i) := by
  rw [Fin.prod_univ_succ]
  congr 1

theorem boxChain_integrand_measurable (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ i, Measurable (fun p : ℝ × ℝ => K i p.1 p.2))
    (lo hi : Fin n → ℝ) (x₀ : ℝ) :
    Measurable ((Icc lo hi).indicator
      (fun y => ∏ i, K i (endpointPath n x₀ y i.castSucc) (y i))) := by
  apply Measurable.indicator _ measurableSet_Icc
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun y : Fin n → ℝ => (endpointPath n x₀ y i.castSucc, y i)) := by
    unfold endpointPath
    fun_prop
  simpa only [Function.comp_def] using! (hK i).comp hm

theorem boxChain_integrand_cons (n : ℕ) (K : Fin (n+1) → ℝ → ℝ → ℝ≥0∞)
    (lo hi : Fin (n+1) → ℝ) (x₀ a : ℝ) (y : Fin n → ℝ) :
    (Icc lo hi).indicator
        (fun z => ∏ i, K i (endpointPath (n+1) x₀ z i.castSucc) (z i)) (Fin.cons a y) =
      (Icc (lo 0) (hi 0)).indicator (fun a => K 0 x₀ a *
        (Icc (Fin.tail lo) (Fin.tail hi)).indicator
          (fun y => ∏ i : Fin n, K i.succ (endpointPath n a y i.castSucc) (y i)) y) a := by
  classical
  by_cases ha : a ∈ Icc (lo 0) (hi 0)
  · by_cases hy : y ∈ Icc (Fin.tail lo) (Fin.tail hi)
    · rw [Set.indicator_of_mem ((cons_mem_box_iff lo hi a y).2 ⟨ha, hy⟩),
        Set.indicator_of_mem ha, Set.indicator_of_mem hy]
      exact endpoint_kernel_product_cons n K x₀ a y
    · rw [Set.indicator_of_notMem (by intro h; exact hy ((cons_mem_box_iff lo hi a y).1 h).2),
        Set.indicator_of_mem ha, Set.indicator_of_notMem hy, mul_zero]
  · rw [Set.indicator_of_notMem (by intro h; exact ha ((cons_mem_box_iff lo hi a y).1 h).1),
      Set.indicator_of_notMem ha]

theorem boxChainIntegral_succ (n : ℕ) (K : Fin (n+1) → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ i, Measurable (fun p : ℝ × ℝ => K i p.1 p.2))
    (hfinite : ∀ i x x', K i x x' ≠ ⊤)
    (lo hi : Fin (n+1) → ℝ) (x₀ : ℝ) :
    boxChainIntegral (n+1) K lo hi x₀ =
      ∫⁻ a in Icc (lo 0) (hi 0), K 0 x₀ a *
        boxChainIntegral n (fun i => K i.succ) (Fin.tail lo) (Fin.tail hi) a := by
  rw [← lintegral_indicator measurableSet_Icc]
  unfold boxChainIntegral
  rw [lintegral_fin_cons n _ (boxChain_integrand_measurable (n+1) K hK lo hi x₀)]
  simp_rw [boxChain_integrand_cons]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ Icc (lo 0) (hi 0)
  · simp only [Set.indicator_of_mem ha]
    exact lintegral_const_mul' _ _ (hfinite 0 x₀ a)
  · simp only [Set.indicator_of_notMem ha, lintegral_zero]

theorem boxChainIntegral_zero (K : Fin 0 → ℝ → ℝ → ℝ≥0∞)
    (lo hi : Fin 0 → ℝ) (x₀ : ℝ) : boxChainIntegral 0 K lo hi x₀ = 1 := by
  have hbox : Icc lo hi = univ := by
    ext y
    simp only [mem_Icc, mem_univ, iff_true]
    constructor <;> intro i <;> exact Fin.elim0 i
  simp [boxChainIntegral, hbox, volume_pi]

theorem boxChainIntegral_le_one (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ i, Measurable (fun p : ℝ × ℝ => K i p.1 p.2))
    (hfinite : ∀ i x x', K i x x' ≠ ⊤)
    (hrow : ∀ i x, (∫⁻ x' : ℝ, K i x x') ≤ 1)
    (lo hi : Fin n → ℝ) (x₀ : ℝ) : boxChainIntegral n K lo hi x₀ ≤ 1 := by
  induction n generalizing x₀ with
  | zero => rw [boxChainIntegral_zero]
  | succ n ih =>
    rw [boxChainIntegral_succ n K hK hfinite lo hi x₀]
    calc
      _ ≤ ∫⁻ a in Icc (lo 0) (hi 0), K 0 x₀ a := by
        apply lintegral_mono
        intro a
        have hh := ih (fun i => K i.succ) (fun i => hK i.succ) (fun i => hfinite i.succ)
          (fun i => hrow i.succ) (Fin.tail lo) (Fin.tail hi) a
        calc
          _ ≤ K 0 x₀ a*1 := mul_le_mul' le_rfl hh
          _ = K 0 x₀ a := mul_one _
      _ ≤ ∫⁻ a : ℝ, K 0 x₀ a := setLIntegral_le_lintegral _ _
      _ ≤ 1 := hrow 0 x₀

#print axioms cons_mem_box_iff
#print axioms endpointPath_cons_tail
#print axioms endpoint_kernel_product_cons
#print axioms boxChain_integrand_measurable
#print axioms boxChain_integrand_cons
#print axioms boxChainIntegral_succ
#print axioms boxChainIntegral_zero
#print axioms boxChainIntegral_le_one

end ConditionalSpectralExtremes
