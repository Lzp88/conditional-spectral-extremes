import TiltedMaximalConcentration
import TiltedDensityDefinitions

/-! Actual pointwise bridge integrals: n free increments, followed by the
prescribed total minus their sum. Thus the path has q=n+1 increments and
the integral is genuinely (q-1)-dimensional Lebesgue integration. Extended
nonnegative integrals retain their meaning before finiteness is established.+-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def bridgePath (n : ℕ) (d : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc x (d - ∑ i, x i)

def bridgeTube (q : ℕ) (d R : ℝ) : Set (Fin q → ℝ) :=
  {x | ∀ j ≤ q, |FiniteWalk.partialSum j x - (j : ℝ) / (q : ℝ) * d| ≤ R}

def pointwiseBridge (f : ℝ → ℝ) (n : ℕ) (d : ℝ)
    (E : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → ℝ, E.indicator
    (fun y => ∏ i, ENNReal.ofReal (f (y i))) (bridgePath n d x)

def tubeBridge (β : ℝ) (n : ℕ) (d R : ℝ) : ℝ≥0∞ :=
  pointwiseBridge (tiltedDensity β) n d (bridgeTube (n+1) d R)

theorem bridgePath_sum (n : ℕ) (d : ℝ) (x : Fin n → ℝ) :
    (∑ i, bridgePath n d x i) = d := by
  simp [bridgePath]

theorem bridgePath_castSucc (n : ℕ) (d : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    bridgePath n d x i.castSucc = x i := by simp [bridgePath]

theorem bridgePath_last (n : ℕ) (d : ℝ) (x : Fin n → ℝ) :
    bridgePath n d x (Fin.last n) = d - ∑ i, x i := by simp [bridgePath]

theorem pointwiseBridge_univ (f : ℝ → ℝ) (n : ℕ) (d : ℝ) :
    pointwiseBridge f n d univ =
      ∫⁻ x : Fin n → ℝ, (∏ i, ENNReal.ofReal (f (x i))) *
        ENNReal.ofReal (f (d - ∑ i, x i)) := by
  unfold pointwiseBridge
  simp only [indicator_univ]
  apply lintegral_congr
  intro x
  rw [Fin.prod_univ_castSucc]
  simp only [bridgePath_castSucc, bridgePath_last]

theorem pointwiseBridge_mono (f : ℝ → ℝ) (n : ℕ) (d : ℝ)
    {E F : Set (Fin (n+1) → ℝ)} (hEF : E ⊆ F) :
    pointwiseBridge f n d E ≤ pointwiseBridge f n d F := by
  apply lintegral_mono
  intro x
  exact Set.indicator_le_indicator_of_subset hEF (fun _ => bot_le)
    (bridgePath n d x)

theorem tiltedDensity_change_tilt (s β x : ℝ) :
    tiltedDensity s x = Real.exp ((s-β)*x + lambda β - lambda s) * tiltedDensity β x := by
  rw [tiltedDensity_eq_weight, tiltedDensity_eq_weight]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem product_density_change_tilt (s β : ℝ) (q : ℕ) (x : Fin q → ℝ) :
    (∏ i, tiltedDensity s (x i)) =
      Real.exp ((s-β)*(∑ i, x i) + (q : ℝ)*(lambda β-lambda s)) *
        ∏ i, tiltedDensity β (x i) := by
  simp_rw [tiltedDensity_change_tilt s β]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem pointwiseBridge_change_tilt (s β : ℝ) (n : ℕ) (d : ℝ)
    (E : Set (Fin (n+1) → ℝ)) :
    pointwiseBridge (tiltedDensity s) n d E =
      ENNReal.ofReal (Real.exp ((n+1 : ℕ)*(lambda β-lambda s) - (β-s)*d)) *
        pointwiseBridge (tiltedDensity β) n d E := by
  classical
  unfold pointwiseBridge
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  by_cases hx : bridgePath n d x ∈ E
  · simp only [Set.indicator_of_mem hx]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => tiltedDensity_nonneg s _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => tiltedDensity_nonneg β _),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), product_density_change_tilt,
      bridgePath_sum]
    congr 3
    push_cast
    ring
  · simp only [Set.indicator_of_notMem hx, mul_zero]

theorem tubeBridge_change_tilt (s β : ℝ) (n : ℕ) (d R : ℝ) :
    tubeBridge s n d R =
      ENNReal.ofReal (Real.exp ((n+1 : ℕ)*(lambda β-lambda s) - (β-s)*d)) *
        tubeBridge β n d R :=
  pointwiseBridge_change_tilt s β n d _

#print axioms bridgePath_sum
#print axioms bridgePath_castSucc
#print axioms bridgePath_last
#print axioms pointwiseBridge_univ
#print axioms pointwiseBridge_mono
#print axioms tiltedDensity_change_tilt
#print axioms product_density_change_tilt
#print axioms pointwiseBridge_change_tilt
#print axioms tubeBridge_change_tilt

end ConditionalSpectralExtremes
