import Mathlib

/-! A finite independent-block squared-energy bound from fourth moments.
The variance identity and Chebyshev step are proved here; subsequent
Poisson instantiations supply the actual moments and independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem independent_fourth_energy_tail {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (F : J → Ω → ℝ)
    (hF : ∀ j, Measurable (F j)) (hI : Pairwise (fun i j => IndepFun (F i) (F j) ν))
    (K : ℝ) (hK : 0 ≤ K) (hJ : 0 < Fintype.card J)
    (hInt : ∀ j, Integrable (fun ω => (F j ω)^4) ν)
    (hMom : ∀ j, (∫ ω, (F j ω)^4 ∂ν) ≤ K) :
    ν.real {ω | 2*(K+1)*(Fintype.card J : ℝ) ≤ ∑ j, (F j ω)^2} ≤
      K/((K+1)^2*(Fintype.card J : ℝ)) := by
  let Y (j : J) (ω : Ω) : ℝ := (F j ω)^2
  have hY (j : J) : Measurable (Y j) := (hF j).pow_const 2
  have hY2 (j : J) : MemLp (Y j) 2 ν := by
    apply (memLp_two_iff_integrable_sq (hY j).aestronglyMeasurable).mpr
    simpa only [Y, ← pow_mul, Nat.reduceMul] using hInt j
  have hYi (j : J) : Integrable (Y j) ν := (hY2 j).integrable (by norm_num)
  have hYI : Pairwise (fun i j => IndepFun (Y i) (Y j) ν) := by
    intro i j hij
    exact (hI hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hMean (j : J) : (∫ ω, Y j ω ∂ν) ≤ K+1 := by
    have hi := (integrable_const (1 : ℝ) (μ := ν)).add (hInt j)
    dsimp only [Pi.add_def] at hi
    have hh := integral_mono (hYi j) hi (fun ω => by
      dsimp only [Y]
      nlinarith [sq_nonneg ((F j ω)^2-1/2)])
    rw [integral_add (integrable_const _) (hInt j), integral_const] at hh
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hh
    linarith [hMom j]
  have hVar (j : J) : variance (Y j) ν ≤ K := by
    have hh := variance_le_expectation_sq (μ := ν) (X := Y j) (hY j).aestronglyMeasurable
    have he : (Y j)^2 = fun ω => (F j ω)^4 := by
      funext ω
      dsimp only [Y, Pi.pow_apply]
      ring
    rw [he] at hh
    exact hh.trans (hMom j)
  let Z (ω : Ω) : ℝ := ∑ j, Y j ω
  have hZ : MemLp Z 2 ν := memLp_finsetSum _ (fun j _ => hY2 j)
  have hZM : (∫ ω, Z ω ∂ν) ≤ (K+1)*(Fintype.card J : ℝ) := by
    rw [show Z = fun ω => ∑ j, Y j ω from rfl, integral_finsetSum _ (fun j _ => hYi j)]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hMean j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm (Fintype.card J : ℝ)] using hh
  have hZV : variance Z ν ≤ K*(Fintype.card J : ℝ) := by
    have he : Z = ∑ j, Y j := by funext ω; simp only [Z, Finset.sum_apply]
    rw [he, IndepFun.variance_sum (fun j _ => hY2 j) (fun i _ j _ hij => hYI hij)]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hVar j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm (Fintype.card J : ℝ)] using hh
  have hJr : 0 < (Fintype.card J : ℝ) := by exact_mod_cast hJ
  have hd : 0 < (K+1)*(Fintype.card J : ℝ) := mul_pos (by linarith) hJr
  have hc := meas_ge_le_variance_div_sq hZ hd
  have hcr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hcr
  have hsub : {ω | 2*(K+1)*(Fintype.card J : ℝ) ≤ ∑ j, (F j ω)^2} ⊆
      {ω | (K+1)*(Fintype.card J : ℝ) ≤ |Z ω-(∫ ω, Z ω ∂ν)|} := by
    intro ω hω
    change 2*(K+1)*(Fintype.card J : ℝ) ≤ Z ω at hω
    apply (show (K+1)*(Fintype.card J : ℝ) ≤ Z ω-(∫ ω, Z ω ∂ν) by linarith).trans
    exact le_abs_self _
  calc
    _ ≤ ν.real {ω | (K+1)*(Fintype.card J : ℝ) ≤ |Z ω-(∫ ω, Z ω ∂ν)|} := measureReal_mono hsub
    _ ≤ variance Z ν / ((K+1)*(Fintype.card J : ℝ))^2 := hcr
    _ ≤ (K*(Fintype.card J : ℝ))/((K+1)*(Fintype.card J : ℝ))^2 :=
      div_le_div_of_nonneg_right hZV (sq_nonneg _)
    _ = _ := by field_simp

#print axioms independent_fourth_energy_tail

end ConditionalSpectralExtremes.BlockCounts
