import FiniteExponentialMaximal
import TiltedConcentration

/-! The manuscript's exponential maximal-deviation estimate on the actual
finite iid tilted log-sine product probability space. The first-passage
maximal theorem is proved in FiniteExponentialMaximal and instantiated
here with actual centered log-sine increments and their proved moments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace ConditionalSpectralExtremes

theorem centeredLogSine_integrable (β : ℝ) (hβ : -1 < β) :
    Integrable (centeredLogSine β) (tiltedLogSineLaw β) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hi : Integrable id (tiltedLogSineLaw β) :=
    memLp_one_iff_integrable.mp (tiltedLogSineLaw_all_moments β hβ 1)
  exact hi.sub (integrable_const _)

theorem centeredLogSine_mgf_ge_one (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    1 ≤ mgf (centeredLogSine β) (tiltedLogSineLaw β) t := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hi := (centeredLogSine_integrable β hβ).const_mul t
  have hh := integral_mono (hi.add (integrable_const (1 : ℝ)))
    (centeredLogSine_exp_integrable β t hβ ht) (fun x => Real.add_one_le_exp (t * centeredLogSine β x))
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const _), integral_const_mul, centeredLogSine_mean_zero β hβ] at hh
  simpa [mgf] using! hh

def centeredLogSinePartial (β : ℝ) {q : ℕ} (j : ℕ) (ω : Fin q → ℝ) : ℝ :=
  FiniteWalk.partialSum j (fun i => centeredLogSine β (ω i))

def scaledLogSineIncrement (β σ : ℝ) {q : ℕ} (i : Fin q) (ω : Fin q → ℝ) : ℝ :=
  σ * centeredLogSine β (ω i)

theorem scaledLogSineIncrement_independent (β σ : ℝ) (q : ℕ) (hβ : -1 < β) :
    iIndepFun (scaledLogSineIncrement β σ) (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  exact iIndepFun_pi (fun _ => (show Measurable (fun x : ℝ => σ * centeredLogSine β x) by
    unfold centeredLogSine; fun_prop).aemeasurable)

theorem scaledLogSineIncrement_measurable (β σ : ℝ) (q : ℕ) (i : Fin q) :
    Measurable (scaledLogSineIncrement β σ i) := by
  unfold scaledLogSineIncrement centeredLogSine
  fun_prop

theorem scaledLogSineIncrement_exp_integrable (β σ t : ℝ) (q : ℕ) (i : Fin q)
    (hβ : -1 < β) (ht : -1 < β + σ * t) :
    Integrable (fun ω => Real.exp (t * scaledLogSineIncrement β σ i ω))
      (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hh := integrable_comp_eval (μ := fun _ : Fin q => tiltedLogSineLaw β)
    (i := i) (centeredLogSine_exp_integrable β (σ * t) hβ ht)
  simpa only [scaledLogSineIncrement, tiltedLogSineProduct, mul_left_comm, mul_assoc] using hh

theorem scaledLogSineIncrement_mgf (β σ t : ℝ) (q : ℕ) (i : Fin q) (hβ : -1 < β) :
    mgf (scaledLogSineIncrement β σ i) (tiltedLogSineProduct β q) t =
      mgf (centeredLogSine β) (tiltedLogSineLaw β) (σ * t) := by
  unfold scaledLogSineIncrement
  rw [mgf_const_mul]
  unfold mgf
  rw [← tiltedLogSineProduct_marginal β q hβ i]
  rw [integral_map (measurable_pi_apply i).aemeasurable (by
    unfold centeredLogSine; fun_prop)]

theorem scaledLogSineIncrement_partial (β σ : ℝ) (q j : ℕ) (ω : Fin q → ℝ) :
    FiniteWalk.randomPartialSum (scaledLogSineIncrement β σ) j ω =
      σ * centeredLogSinePartial β j ω := by
  simp only [FiniteWalk.randomPartialSum, FiniteWalk.partialSum, scaledLogSineIncrement,
    centeredLogSinePartial, Finset.mul_sum]

theorem centeredLogSinePartial_full (β : ℝ) (q : ℕ) (ω : Fin q → ℝ) :
    centeredLogSinePartial β q ω = centeredLogSineSum β ω :=
  FiniteWalk.partialSum_full q (fun i => centeredLogSine β (ω i))

/-- Exact signed exponential maximal inequality, on the actual product law.
The constant has no multiplicative factor q. -/
theorem centeredLogSinePartial_signed_maximal (β σ t w : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + σ * t) (ht0 : 0 ≤ t) :
    (tiltedLogSineProduct β q).real {ω | ∃ j ≤ q, w ≤ σ * centeredLogSinePartial β j ω} ≤
      Real.exp (-t * w + (q : ℝ) *
        (lambda (β + σ * t) - lambda β - (σ * t) * deriv lambda β)) := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hβ
  have hh := FiniteWalk.exponential_maximal (scaledLogSineIncrement β σ)
    (scaledLogSineIncrement_independent β σ q hβ) (scaledLogSineIncrement_measurable β σ q)
    t w ht0 (fun i => scaledLogSineIncrement_exp_integrable β σ t q i hβ ht)
    (fun i => by rw [scaledLogSineIncrement_mgf β σ t q i hβ]
                 exact centeredLogSine_mgf_ge_one β (σ * t) hβ ht)
  have hfull : FiniteWalk.randomPartialSum (scaledLogSineIncrement β σ) q =
      fun ω : Fin q → ℝ => σ * centeredLogSineSum β ω := by
    funext ω
    rw [scaledLogSineIncrement_partial, centeredLogSinePartial_full]
  rw [hfull, mgf_const_mul, centeredLogSineSum_mgf β (σ * t) q hβ ht, ← Real.exp_add] at hh
  simpa only [scaledLogSineIncrement_partial] using hh

/-- Compact-uniform two-sided maximal moderate deviations, with explicit
dependence on the two constants furnished by the actual lambda curvature. -/
theorem centeredLogSinePartial_maximal_moderate_deviation (a b : ℝ)
    (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ β ∈ Icc a b, ∀ q : ℕ, 0 < q →
      ∀ w : ℝ, 0 ≤ w → w ≤ 2 * M * δ * (q : ℝ) →
        (tiltedLogSineProduct β q).real {ω | ∃ j ≤ q, w ≤ |centeredLogSinePartial β j ω|} ≤
          2 * Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
  obtain ⟨δ, M, hδ, hM, hh⟩ := lambda_uniform_quadratic_cumulant a b ha hab
  refine ⟨δ, M, hδ, hM, ?_⟩
  intro β hβ q hq w hw hwrange
  have hb := lt_of_lt_of_le ha hβ.1
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hb
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let r := w / (2 * M * (q : ℝ))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrδ : |r| ≤ δ := by
    rw [abs_of_nonneg hr0]
    apply (div_le_iff₀ (by positivity : 0 < 2 * M * (q : ℝ))).mpr
    nlinarith only [hwrange]
  obtain ⟨hbr, hqr⟩ := hh β hβ r hrδ
  obtain ⟨hbn, hqn⟩ := hh β hβ (-r) (by simpa only [abs_neg] using hrδ)
  have hupper : (tiltedLogSineProduct β q).real
      {ω | ∃ j ≤ q, w ≤ centeredLogSinePartial β j ω} ≤
      Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
    have hmax := centeredLogSinePartial_signed_maximal β 1 r w q hb (by simpa using hbr) hr0
    simp only [one_mul] at hmax
    calc
      _ ≤ Real.exp (-r * w + (q : ℝ) *
          (lambda (β + r) - lambda β - r * deriv lambda β)) := hmax
      _ ≤ Real.exp (-r * w + (q : ℝ) * (M * r ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith only [mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqr) hq'.le]
      _ = _ := by
        congr 1
        dsimp [r]
        field_simp
        ring
  have hlower : (tiltedLogSineProduct β q).real
      {ω | ∃ j ≤ q, w ≤ -centeredLogSinePartial β j ω} ≤
      Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
    have hmax := centeredLogSinePartial_signed_maximal β (-1) r w q hb (by simpa using hbn) hr0
    simp only [neg_one_mul] at hmax
    calc
      _ ≤ Real.exp (-r * w + (q : ℝ) *
          (lambda (β + -r) - lambda β - (-r) * deriv lambda β)) := hmax
      _ ≤ Real.exp (-r * w + (q : ℝ) * (M * (-r) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith only [mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqn) hq'.le]
      _ = _ := by
        congr 1
        dsimp [r]
        field_simp
        ring
  have he : {ω : Fin q → ℝ | ∃ j ≤ q, w ≤ |centeredLogSinePartial β j ω|} =
      {ω | ∃ j ≤ q, w ≤ centeredLogSinePartial β j ω} ∪
      {ω | ∃ j ≤ q, w ≤ -centeredLogSinePartial β j ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs]
    aesop
  rw [he]
  exact (measureReal_union_le _ _).trans ((add_le_add hupper hlower).trans_eq (by ring))

/-- Manuscript Lemma walk's maximal estimate on the actual product law.
There is one uniform c>0 and the prefactor is exactly 2, independent of q. -/
theorem walk_maximal_deviation (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ β ∈ Icc a b, ∀ q : ℕ, 0 < q →
      ∀ w : ℝ, 1 ≤ w → w ≤ c * (q : ℝ) →
        (tiltedLogSineProduct β q).real {ω | ∃ j ≤ q, w ≤ |centeredLogSinePartial β j ω|} ≤
          2 * Real.exp (-c * w ^ 2 / (q : ℝ)) := by
  obtain ⟨δ, M, hδ, hM, hh⟩ := centeredLogSinePartial_maximal_moderate_deviation a b ha hab
  let c := min (2 * M * δ) (1 / (4 * M))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro β hβ q hq w hw hwrange
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hwrange' : w ≤ 2 * M * δ * (q : ℝ) := hwrange.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hq'.le)
  apply (hh β hβ q hq w (by linarith) hwrange').trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hneg : -(w ^ 2) / (4 * M) ≤ -c * w ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right (show c ≤ 1 / (4 * M) from min_le_right _ _) (sq_nonneg w)
    rw [div_eq_mul_inv, one_mul] at hm
    rw [div_eq_mul_inv]
    nlinarith only [hm]
  simpa only [div_mul_eq_div_div] using (div_le_div_of_nonneg_right hneg hq'.le)

#print axioms centeredLogSine_integrable
#print axioms centeredLogSine_mgf_ge_one
#print axioms scaledLogSineIncrement_independent
#print axioms scaledLogSineIncrement_measurable
#print axioms scaledLogSineIncrement_exp_integrable
#print axioms scaledLogSineIncrement_mgf
#print axioms scaledLogSineIncrement_partial
#print axioms centeredLogSinePartial_full
#print axioms centeredLogSinePartial_signed_maximal
#print axioms centeredLogSinePartial_maximal_moderate_deviation
#print axioms walk_maximal_deviation

end ConditionalSpectralExtremes
