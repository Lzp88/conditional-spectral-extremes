import PairBox
import NoiseFourierMass

/-! The joint noise Fourier mass outside a square, with a genuine product-tail estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

theorem pairUniformNoise_frequency_tail_product (δ T : Real) (hδ : 0 < δ) :
    (∫ u in (pairBox T)ᶜ, ‖charFun (pairUniformNoise δ) u‖) ≤
      2*(∫ u in (Icc (-T) T)ᶜ, ‖charFun (tenUniformNoise δ) u‖)*
        (∫ u, ‖charFun (tenUniformNoise δ) u‖) := by
  let F : Real → Real := fun u => ‖charFun (tenUniformNoise δ) u‖
  let O : Real → Real := (Icc (-T) T)ᶜ.indicator F
  have hF : Integrable F := (tenUniformNoise_charFun_integrable δ hδ).norm
  have hO : Integrable O := hF.indicator measurableSet_Icc.compl
  have hpos (u : PairSpace) : 0 ≤ (pairBox T)ᶜ.indicator (fun u => ‖charFun (pairUniformNoise δ) u‖) u :=
    indicator_nonneg (fun _ _ => norm_nonneg _) u
  rw [← integral_indicator (measurableSet_pairBox T).compl,
    ← (WithLp.volume_preserving_toLp Real Real).integral_comp
      (MeasurableEquiv.toLp 2 (Real × Real)).measurableEmbedding]
  have hp (z : Real × Real) :
      (pairBox T)ᶜ.indicator (fun u => ‖charFun (pairUniformNoise δ) u‖) (toLp 2 z) ≤
        O z.1*F z.2+F z.1*O z.2 := by
    classical
    simp only [Set.indicator]
    have hb : toLp 2 z ∈ pairBox T ↔ z.1 ∈ Icc (-T) T ∧ z.2 ∈ Icc (-T) T := Iff.rfl
    simp only [mem_compl_iff, hb]
    rw [pairUniformNoise_charFun δ hδ, norm_mul]
    change (if ¬ (z.1 ∈ Icc (-T) T ∧ z.2 ∈ Icc (-T) T) then F z.1*F z.2 else 0) ≤ _
    have hn (x : Real) : 0 ≤ F x := norm_nonneg _
    by_cases hx : z.1 ∈ Icc (-T) T <;> by_cases hy : z.2 ∈ Icc (-T) T
    all_goals simp [O, hx, hy]
    exact mul_nonneg (hn _) (hn _)
  have hi := (hO.mul_prod hF).add (hF.mul_prod hO)
  calc
    _ ≤ ∫ z : Real × Real, O z.1*F z.2+F z.1*O z.2 :=
      integral_mono_of_nonneg (ae_of_all _ (fun z => hpos (toLp 2 z))) hi (ae_of_all _ hp)
    _ = (∫ u, O u)*(∫ u, F u)+(∫ u, F u)*(∫ u, O u) := by
      have hadd : (∫ z : Real × Real, O z.1*F z.2+F z.1*O z.2) =
          (∫ z : Real × Real, O z.1*F z.2)+(∫ z : Real × Real, F z.1*O z.2) := by
        convert! integral_add (hO.mul_prod hF) (hF.mul_prod hO) using 1
      rw [hadd]
      congr 1
      · convert! integral_prod_mul (μ := (volume : Measure Real)) (ν := (volume : Measure Real)) O F using 1
      · convert! integral_prod_mul (μ := (volume : Measure Real)) (ν := (volume : Measure Real)) F O using 1
    _ = _ := by
      dsimp only [O, F]
      rw [integral_indicator measurableSet_Icc.compl]
      ring

theorem pairUniformNoise_frequency_tail (δ T : Real) (hδ : 0 < δ) (hT : 0 < T) :
    (∫ u in (pairBox T)ᶜ, ‖charFun (pairUniformNoise δ) u‖) ≤
      2*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9)*((200/9 : Real)/δ) := by
  apply (pairUniformNoise_frequency_tail_product δ T hδ).trans
  have htail := tenUniformNoise_frequency_tail δ T hδ hT
  have hmass := tenUniformNoise_frequency_mass δ hδ
  have hM : 0 ≤ ∫ u, ‖charFun (tenUniformNoise δ) u‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hB : 0 ≤ 2*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left htail (by norm_num)) hmass hM hB

#print axioms pairUniformNoise_frequency_tail
end ConditionalSpectralAudit.FourierHarmonic
