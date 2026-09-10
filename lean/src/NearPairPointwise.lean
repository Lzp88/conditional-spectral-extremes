import RawPathQuality
import PathNoiseAbsorption

/-! The actual close-pair Markov inequality. The two prefixes are never
assumed independent: the first point is retained through every block,
and the second point is retained only after the separation block.
Every spectral root keeps its true zero in Z and in the norm powers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

def rawNearMixedFactor {m : ℕ} {q : ℕ → ℕ} (s : ℝ) (k : ℕ)
    (t u : AddCircle (1 : ℝ)) (x : (i : Fin m) → Fin (q i) → ℕ) : ℝ :=
  ∏ i, if i.val < k then rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) (x i)
    else rawHarmonicBlockVectorFactor s ![t,u] (x i)

theorem rawNearMixedFactor_nonneg {m : ℕ} {q : ℕ → ℕ} (s : ℝ) (k : ℕ)
    (t u : AddCircle (1 : ℝ)) (x : (i : Fin m) → Fin (q i) → ℕ) :
    0 ≤ rawNearMixedFactor s k t u x := by
  unfold rawNearMixedFactor
  apply Finset.prod_nonneg
  intro i _
  split <;> exact rawHarmonicBlockVectorFactor_nonneg _ _ _

theorem raw_one_block_factor_exponential {q : ℕ} (s : ℝ)
    (t : AddCircle (1 : ℝ)) (x : Fin q → ℕ)
    (hr : ∀ v, ‖(1 : ℂ)-fourier 1 (x v • t)‖ ≠ 0) :
    rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) x =
      Real.exp (s*∑ v, logSine (x v • t)) := by
  have he (v : Fin q) : ‖(1 : ℂ)-fourier 1 (x v • t)‖^s =
      Real.exp (s*logSine (x v • t)) := by
    rw [Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hr v)))]
    unfold logSine
    congr 1
    ring
  unfold rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
  simp only [Fin.prod_univ_one]
  simp_rw [he, ← Real.exp_sum, ← Finset.mul_sum]

theorem raw_pair_block_factor_product {q : ℕ} (s : ℝ)
    (t u : AddCircle (1 : ℝ)) (x : Fin q → ℕ) :
    rawHarmonicBlockVectorFactor s ![t,u] x =
      rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) x *
        rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => u) x := by
  simp only [rawHarmonicBlockVectorFactor, rawHarmonicVectorFactor,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_one,
    Finset.prod_mul_distrib]

theorem rawNearMixedFactor_exponential {m : ℕ} {q : ℕ → ℕ} (s : ℝ) (k : ℕ)
    (t u : AddCircle (1 : ℝ)) (x : (i : Fin m) → Fin (q i) → ℕ)
    (ht : rawMiddleRootFree t x) (hu : rawMiddleRootFree u x) :
    rawNearMixedFactor s k t u x =
      Real.exp (s*(∑ i, ∑ v, logSine (x i v • t)) +
        s*((∑ i, ∑ v, logSine (x i v • u)) -
          FiniteWalk.partialSum k (fun i => ∑ v, logSine (x i v • u)))) := by
  have he (i : Fin m) :
      (if i.val < k then rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) (x i)
        else rawHarmonicBlockVectorFactor s ![t,u] (x i)) =
      Real.exp (s*(∑ v, logSine (x i v • t)) +
        s*((∑ v, logSine (x i v • u)) - if i.val < k then ∑ v, logSine (x i v • u) else 0)) := by
    by_cases hi : i.val < k
    · rw [if_pos hi, if_pos hi, raw_one_block_factor_exponential s t (x i) (ht i)]
      congr 1
      ring
    · rw [if_neg hi, if_neg hi, raw_pair_block_factor_product,
        raw_one_block_factor_exponential s t (x i) (ht i),
        raw_one_block_factor_exponential s u (x i) (hu i), ← Real.exp_add]
      congr 1
      ring
  unfold rawNearMixedFactor
  simp_rw [he, ← Real.exp_sum]
  congr 1
  simp only [FiniteWalk.partialSum, FiniteWalk.prefixIndices, Finset.sum_filter,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem near_noise_exponent (m k : ℕ) (s y B δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (X Y ζ ξ : Fin m → ℝ)
    (hX : y ≤ ∑ i, (X+ζ) i) (hY : y ≤ ∑ i, (Y+ξ) i)
    (hprefix : FiniteWalk.partialSum k (Y+ξ) ≤ B) (hξ : ∀ i, |ξ i| ≤ δ) :
    -s*(∑ i, ζ i)-s*(∑ i, ξ i) ≤
      -2*s*y+s*B+s*((m : ℝ)*δ)+s*(∑ i, X i)+
        s*((∑ i, Y i)-FiniteWalk.partialSum k Y) := by
  have hn := (abs_le.mp (bounded_noise_partialSum m k δ hδ ξ hξ)).1
  rw [fine_partialSum_add] at hprefix
  simp only [Pi.add_apply, Finset.sum_add_distrib] at hX hY
  have ha := mul_le_mul_of_nonneg_left hX hs
  have hb := mul_le_mul_of_nonneg_left hY hs
  have hc := mul_le_mul_of_nonneg_left hprefix hs
  have hd := mul_le_mul_of_nonneg_left hn hs
  nlinarith

theorem raw_near_pair_integrand_bound (p : FineScales.Parameters) (n : ℕ)
    (κ G δ : ℝ) (hκ : 0 < κ) (hδ : 0 ≤ δ) (q : ℕ → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ FineScales.count p n)
    (t u : AddCircle (1 : ℝ)) (x : FineRawSample p n q)
    (ζ ξ : Fin (FineScales.count p n) → ℝ) (hξ : ∀ i, |ξ i| ≤ δ) :
    rawPathQualityIntegrand p n κ G q t x ζ * rawPathQualityIntegrand p n κ G q u x ξ ≤
      ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
        criticalPoint κ*(fineFrontier p n κ q k-G) +
        criticalPoint κ*((FineScales.count p n : ℝ)*δ))) *
      ENNReal.ofReal (rawNearMixedFactor (q := fun i => q (i+1)) (criticalPoint κ) k t u x) := by
  classical
  unfold rawPathQualityIntegrand
  by_cases ht : rawMiddleRootFree (q := fun i => q (i+1)) t x
  · rw [if_pos ht]
    by_cases hu : rawMiddleRootFree (q := fun i => q (i+1)) u x
    · rw [if_pos hu]
      by_cases hte : rawFineHeight p n q t x+ζ ∈ pathEvent p n κ G q
      · rw [indicator_of_mem hte]
        by_cases hue : rawFineHeight p n q u x+ξ ∈ pathEvent p n κ G q
        · rw [indicator_of_mem hue]
          have hp : FiniteWalk.partialSum k (rawFineHeight p n q u x+ξ) ≤
              fineFrontier p n κ q k-G := by
            have h := hue.1 ⟨k-1, by omega⟩
            simpa only [show k-1+1=k by omega] using h
          have hX := hte.2.1
          have hY := hue.2.1
          rw [full_partialSum_eq_sum] at hX hY
          have he := near_noise_exponent (FineScales.count p n) k (criticalPoint κ)
            (terminalHeight p n κ q) (fineFrontier p n κ q k-G) δ (criticalPoint_pos hκ).le
            hδ (rawFineHeight p n q t x) (rawFineHeight p n q u x) ζ ξ hX hY hp hξ
          rw [rawNearMixedFactor_exponential _ _ _ _ _ ht hu,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_add]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          simp only [rawFineHeight, rawHarmonicMiddleHeight, rawHarmonicBlockHeight,
            vectorSum, harmonicHeight] at he
          have hraw : rawFineHeight p n q u x = (fun i => ∑ v, logSine (x i v • u)) := rfl
          rw [hraw] at he
          convert he using 1 <;> ring
        · rw [indicator_of_notMem hue, mul_zero]
          positivity
      · rw [indicator_of_notMem hte, zero_mul]
        positivity
    · rw [if_neg hu, mul_zero]
      positivity
  · rw [if_neg ht, zero_mul]
    positivity

#print axioms rawNearMixedFactor_nonneg
#print axioms rawNearMixedFactor_exponential
#print axioms near_noise_exponent
#print axioms raw_near_pair_integrand_bound
end ConditionalSpectralAudit.FourierHarmonic
