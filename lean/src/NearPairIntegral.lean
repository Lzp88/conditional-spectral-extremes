import NearPairScaledMoment
import NearClassSeparation

/-! Actual close-pair integration on the two-torus. Every arithmetic
class is covered, including arbitrarily close pairs in the final class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes ArithmeticArcs

def rawPairExpectation (p : FineScales.Parameters) (n : ℕ) (κ G δ : ℝ)
    (q lo hi : ℕ → ℕ) (tu : Torus × Torus) : ℝ≥0∞ :=
  ∫⁻ z, rawPathQuality p n κ G δ q tu.1 z * rawPathQuality p n κ G δ q tu.2 z
    ∂harmonicMiddleSampleLaw lo hi (fun i => q (i+1)) (FineScales.count p n)

def actualNearPairIntegral (p : FineScales.Parameters) (n : ℕ) (κ G δ : ℝ)
    (q lo hi : ℕ → ℕ) (D : Set Torus) (R : ℕ) (Δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ tu in (D ×ˢ D) ∩ badPair R (Real.exp (-FineScales.r p n+Δ)),
    rawPairExpectation p n κ G δ q lo hi tu ∂haar.prod haar

theorem near_area_exponential_cancellation (M R a b ω Δ E : ℝ) (hab : b-a=ω) :
    (M*Real.exp (b+E))*(18*R^2*Real.exp (-a+Δ)) =
      18*R^2*M*Real.exp (ω+Δ+E) := by
  calc
    _ = 18*R^2*M*(Real.exp (b+E)*Real.exp (-a+Δ)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      linarith

theorem actual_near_pair_integral_bound (p : FineScales.Parameters) (n : ℕ)
    (κ G δ pmin P J u₁ u₂ u₃ x : ℝ) (hκ : 0 < κ) (hδ : 0 < δ)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hpoly₁ : PolynomialSmoothingL1One pmin P J u₁ u₂ u₃ x)
    (hpoly₂ : PolynomialSmoothingL1Two pmin P J u₁ u₂ u₃ x)
    (q lo hi : ℕ → ℕ) (D : Set Torus) (hR : 0 < integrationFrequencyCutoff x u₂)
    (hω : 0 ≤ FineScales.omega p n) (hmpos : 0 < FineScales.count p n)
    (hD : ∀ t ∈ D, t ∉ badOne (integrationFrequencyCutoff x u₂)
      (Real.exp (-FineScales.r p n+u₃*Real.log x)))
    (hq : ∀ i < FineScales.count p n, (q (i+1) : ℝ) ≤ x)
    (hm : ∀ i < FineScales.count p n, 0 < lo i)
    (hH : ∀ i < FineScales.count p n, 1 ≤ harmonicMass (lo i) (hi i))
    (ha : ∀ i < FineScales.count p n, Real.exp (FineScales.coordinate p n i) ≤ lo i) :
    actualNearPairIntegral p n κ G δ q lo hi D (integrationFrequencyCutoff x u₂) (u₃*Real.log x) ≤
      ENNReal.ofReal ((FineScales.count p n : ℝ)*18*(integrationFrequencyCutoff x u₂ : ℝ)^2*
        pathMomentScale p n κ q^2 * Real.exp (FineScales.omega p n+u₃*Real.log x-criticalPoint κ*G+
          criticalPoint κ*((FineScales.count p n : ℝ)*δ)+(FineScales.count p n : ℝ)*x^(-J))) := by
  let m := FineScales.count p n
  let R := integrationFrequencyCutoff x u₂
  let Δ := u₃*Real.log x
  let E := -criticalPoint κ*G+criticalPoint κ*((m : ℝ)*δ)+(m : ℝ)*x^(-J)
  let M := pathMomentScale p n κ q^2
  let S (k : Fin m) := (D ×ˢ D) ∩ nearPairClass R m (FineScales.coordinate p n) Δ k
  let f := rawPairExpectation p n κ G δ q lo hi
  have hbound (k : Fin m) (tu : Torus × Torus) (htu : tu ∈ S k) :
      f tu ≤ ENNReal.ofReal (M*Real.exp (FineScales.coordinate p n (k.val+1)+E)) := by
    have hh := actual_raw_near_pair_smoothing p n κ G δ pmin P J u₁ u₂ u₃ x hκ hδ hsp hsP
      hpoly₁ hpoly₂ q lo hi (FineScales.coordinate p n) (k.val+1) (by omega) k.isLt tu.1 tu.2
      hq hm hH ha
      (fun i _ => good_one_separated_all_fine p n R i Δ hω tu.1 (hD tu.1 htu.1.1))
      (fun i him hik => near_class_suffix_separated p n R i Δ hω k hik him tu.1 tu.2 htu.2)
    convert! hh using 1
    congr 3
    ring
  have hclass (k : Fin m) :
      (∫⁻ tu in S k, f tu ∂haar.prod haar) ≤
        ENNReal.ofReal (18*(R : ℝ)^2*M*Real.exp (FineScales.omega p n+Δ+E)) := by
    calc
      _ ≤ ∫⁻ _tu in S k, ENNReal.ofReal (M*Real.exp (FineScales.coordinate p n (k.val+1)+E))
          ∂haar.prod haar := setLIntegral_mono measurable_const (fun tu htu => hbound k tu htu)
      _ = ENNReal.ofReal (M*Real.exp (FineScales.coordinate p n (k.val+1)+E)) * (haar.prod haar) (S k) :=
        setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (M*Real.exp (FineScales.coordinate p n (k.val+1)+E)) *
          ENNReal.ofReal (18*(R : ℝ)^2*Real.exp (-FineScales.coordinate p n k+Δ)) :=
        mul_le_mul_of_nonneg_left ((measure_mono inter_subset_right).trans
          (nearPairClass_area R m hR (FineScales.coordinate p n) Δ k)) (by positivity)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by dsimp [M]; positivity), near_area_exponential_cancellation
          M R (FineScales.coordinate p n k) (FineScales.coordinate p n (k.val+1))
            (FineScales.omega p n) Δ E (near_coordinate_gap p n k)]
  have hcover : (D ×ˢ D) ∩ badPair R (Real.exp (-FineScales.r p n+Δ)) ⊆ ⋃ k : Fin m, S k := by
    intro tu htu
    have hc := badPair_covered_by_classes R m hmpos (FineScales.coordinate p n) Δ
    have ht : tu ∈ badPair R (Real.exp (-FineScales.coordinate p n 0+Δ)) := by
      simpa only [FineScales.coordinate, Nat.cast_zero, zero_mul, add_zero] using htu.2
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hc ht)
    exact mem_iUnion.mpr ⟨k, htu.1, hk⟩
  calc
    _ ≤ ∫⁻ tu in ⋃ k : Fin m, S k, f tu ∂haar.prod haar := lintegral_mono_set hcover
    _ ≤ ∑ k : Fin m, ∫⁻ tu in S k, f tu ∂haar.prod haar := by
      simpa only [tsum_fintype] using lintegral_iUnion_le S f
    _ ≤ ∑ _k : Fin m, ENNReal.ofReal (18*(R : ℝ)^2*M*Real.exp (FineScales.omega p n+Δ+E)) :=
      Finset.sum_le_sum (fun k _ => hclass k)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1
      dsimp only [m, R, M, Δ, E]
      rw [show FineScales.omega p n+u₃*Real.log x+
          (-criticalPoint κ*G+criticalPoint κ*((FineScales.count p n : ℝ)*δ)+
            (FineScales.count p n : ℝ)*x^(-J)) =
        FineScales.omega p n+u₃*Real.log x-criticalPoint κ*G+
          criticalPoint κ*((FineScales.count p n : ℝ)*δ)+(FineScales.count p n : ℝ)*x^(-J) by ring]
      ring

#print axioms near_area_exponential_cancellation
#print axioms actual_near_pair_integral_bound
end ConditionalSpectralAudit.FourierHarmonic
