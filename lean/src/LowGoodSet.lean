import LowFieldBadMeasure
import InitialDiophantineSet

/-! A large measurable angular set selected by any fixed low configuration,
uniformly over its actual positive lengths. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Real ENNReal
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs

def lowGoodSet {q : Nat} (j : Fin q → Nat) (u : Real) : Set Torus :=
  {t | -u ≤ lowLogSineField j t}

theorem lowGoodSet_measurable {q : Nat} (j : Fin q → Nat) (u : Real) :
    MeasurableSet (lowGoodSet j u) := measurableSet_le measurable_const (lowLogSineField_measurable j)

theorem lowGoodSet_compl {q : Nat} (j : Fin q → Nat) (u : Real) :
    (lowGoodSet j u)ᶜ = {t | lowLogSineField j t < -u} := by
  ext t
  simp [lowGoodSet]

theorem low_good_intersection_measure {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v)
    (u δ : Real) (hu : 0 < u) (D : Set Torus) (hD : MeasurableSet D)
    (hDsmall : haar.real Dᶜ ≤ δ) :
    1-δ-(q : Real)*negativeLogSineMass/u ≤ haar.real (D ∩ lowGoodSet j u) := by
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (actual_low_field_bad_measure j hj u hu)
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (Nat.cast_nonneg _) negativeLogSineMass_nonneg) hu.le)] at hb
  have hc := measureReal_compl (μ := haar) (hD.inter (lowGoodSet_measurable j u))
  rw [compl_inter, lowGoodSet_compl] at hc
  have hone : haar.real Set.univ=1 := by simp [measureReal_def]
  rw [hone] at hc
  have hu' := measureReal_union_le (μ := haar) Dᶜ {t | lowLogSineField j t < -u}
  change haar.real {t | lowLogSineField j t < -u} ≤ _ at hb
  linarith

theorem actual_low_good_set_large {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v)
    (K r : Real) (hK : 0 ≤ K) (hr : 0 < r) (hq : (q : Real) ≤ K*r)
    (D : Set Torus) (hD : MeasurableSet D) (hDsmall : haar.real Dᶜ ≤ 1/8) :
    (3/4 : Real) ≤ haar.real (D ∩ lowGoodSet j ((8*K*negativeLogSineMass+1)*r)) := by
  have hC : 0 < 8*K*negativeLogSineMass+1 := by nlinarith [negativeLogSineMass_nonneg]
  have hb : (q : Real)*negativeLogSineMass/((8*K*negativeLogSineMass+1)*r) ≤ 1/8 := by
    apply (div_le_iff₀ (mul_pos hC hr)).mpr
    have hh := mul_le_mul_of_nonneg_right hq negativeLogSineMass_nonneg
    nlinarith
  have hh := low_good_intersection_measure j hj ((8*K*negativeLogSineMass+1)*r) (1/8)
    (mul_pos hC hr) D hD hDsmall
  linarith

#print axioms low_good_intersection_measure
#print axioms actual_low_good_set_large
end ConditionalSpectralExtremes
