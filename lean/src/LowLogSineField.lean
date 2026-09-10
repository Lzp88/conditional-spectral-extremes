import HaarPolynomialMoment
import TiltedLogSine

/-! The actual low log-sine field. Its values at its finitely many roots
are only a real representative; all measure and integral claims are
unchanged by these null points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs

def negativeLogSine (t : Torus) : Real := max (-logSine t) 0
def negativeLogSineMass : Real := ∫ t, negativeLogSine t ∂haar

theorem negativeLogSine_nonneg (t : Torus) : 0 ≤ negativeLogSine t := le_max_right _ _

theorem negative_part_exponential_bound (x : Real) : max (-x) 0 ≤ 2*Real.exp (-x/2) := by
  apply max_le
  · have hh := Real.add_one_le_exp (-x/2)
    linarith
  · positivity

theorem negativeLogSine_integrable : Integrable negativeLogSine haar := by
  apply ((logSine_exp_integrable (-1/2) (by norm_num)).const_mul 2).mono'
    ((logSine_measurable.neg.max measurable_const).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖negativeLogSine t‖ ≤ 2*Real.exp (-1/2*logSine t)
  rw [Real.norm_of_nonneg (negativeLogSine_nonneg t)]
  simpa only [negativeLogSine, neg_div, neg_mul, one_div_mul_eq_div] using
    negative_part_exponential_bound (logSine t)

theorem negativeLogSineMass_nonneg : 0 ≤ negativeLogSineMass :=
  integral_nonneg negativeLogSine_nonneg

theorem logSine_nsmul_integrable (j : Nat) (hj : 0 < j) :
    Integrable (fun t : Torus => negativeLogSine (j • t)) haar := by
  have hp := Measure.measurePreserving_zsmul haar (by exact_mod_cast Nat.ne_of_gt hj : (j : Int) ≠ 0)
  have hh : Integrable negativeLogSine (haar.map (fun t : Torus => (j : Int) • t)) := by
    rw [hp.map_eq]
    exact negativeLogSine_integrable
  simpa only [Function.comp_def, natCast_zsmul] using hh.comp_measurable hp.measurable

theorem negativeLogSine_nsmul_integral (j : Nat) (hj : 0 < j) :
    (∫ t : Torus, negativeLogSine (j • t) ∂haar) = negativeLogSineMass := by
  have hp := Measure.measurePreserving_zsmul haar (by exact_mod_cast Nat.ne_of_gt hj : (j : Int) ≠ 0)
  have hh := integral_map (μ := haar) hp.measurable.aemeasurable
    (f := negativeLogSine) (logSine_measurable.neg.max measurable_const).aestronglyMeasurable
  rw [hp.map_eq] at hh
  simpa only [natCast_zsmul, negativeLogSineMass] using! hh.symm

def lowLogSineField {q : Nat} (j : Fin q → Nat) (t : Torus) : Real :=
  ∑ v, logSine (j v • t)

theorem lowLogSineField_negative_bound {q : Nat} (j : Fin q → Nat) (t : Torus) :
    max (-lowLogSineField j t) 0 ≤ ∑ v, negativeLogSine (j v • t) := by
  apply max_le
  · change -(∑ v, logSine (j v • t)) ≤ _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun _ _ => le_max_left _ _)
  · exact Finset.sum_nonneg (fun _ _ => negativeLogSine_nonneg _)

#print axioms negativeLogSine_integrable
#print axioms negativeLogSine_nsmul_integral
#print axioms lowLogSineField_negative_bound
end ConditionalSpectralExtremes
