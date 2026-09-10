import RawMiddleChangeMeasure
import FinePathComparison

/-! The exact scalar path pushforward of the original middle sample space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem raw_middle_exact_scalar_height_law (s : Real) (t : AddCircle (1 : Real))
    (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < m, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i), harmonicTiltWeight s (fun _ : Fin 1 => t) j) :
    ((harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m).withDensity
      (fun x => ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s (fun _ : Fin 1 => t) x))).map
        (fun x i => rawHarmonicMiddleHeight (q := fun j => q (j+1)) (fun _ : Fin 1 => t) x i 0) =
      ENNReal.ofReal (∏ i : Fin m, harmonicTiltNormalizer s (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1)) •
        fineTiltedLaw s t lo hi q m := by
  let _ (i : Fin m) := harmonicTiltSumLaw_probability s (fun _ : Fin 1 => t)
    (lo i) (hi i) (q (i.val+1)) (hW i i.isLt)
  have hm : Measurable (fun w : Fin m → Fin 1 → Real => fun i => w i 0) := by fun_prop
  have hr : Measurable (@rawHarmonicMiddleHeight 1 m (fun j => q (j+1)) (fun _ => t)) :=
    measurable_of_countable _
  have he := congrArg (fun μ : Measure (Fin m → Fin 1 → Real) =>
    μ.map (fun w i => w i 0))
    (raw_middle_exact_tilted_height_law s (fun _ : Fin 1 => t) lo hi (fun j => q (j+1)) m hH hW)
  rw [Measure.map_map hm hr, Measure.map_smul] at he
  unfold harmonicMiddleTiltLaw at he
  rw [Measure.pi_map_pi (fun _ => (measurable_pi_apply (0 : Fin 1)).aemeasurable)] at he
  exact he

theorem raw_middle_scalar_tilted_integral (s : Real) (t : AddCircle (1 : Real))
    (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < m, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i), harmonicTiltWeight s (fun _ : Fin 1 => t) j)
    (φ : (Fin m → Real) → ENNReal) (hφ : Measurable φ) :
    (∫⁻ x, ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s (fun _ : Fin 1 => t) x) *
      φ (fun i => rawHarmonicMiddleHeight (q := fun j => q (j+1)) (fun _ : Fin 1 => t) x i 0)
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m) =
      ENNReal.ofReal (∏ i : Fin m, harmonicTiltNormalizer s (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1)) *
        ∫⁻ w, φ w ∂fineTiltedLaw s t lo hi q m := by
  have hr : Measurable (fun x : (i : Fin m) → Fin (q (i.val+1)) → Nat =>
      fun i => rawHarmonicMiddleHeight (q := fun j => q (j+1)) (fun _ : Fin 1 => t) x i 0) := measurable_of_countable _
  have hd : Measurable (fun x : (i : Fin m) → Fin (q (i.val+1)) → Nat =>
      ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s (fun _ : Fin 1 => t) x)) := measurable_of_countable _
  have he := lintegral_withDensity_eq_lintegral_mul
    (harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m) hd (hφ.comp hr)
  simp only [Pi.mul_apply, Function.comp_def] at he
  rw [← he, ← lintegral_map hφ hr, raw_middle_exact_scalar_height_law s t lo hi q m hH hW,
    lintegral_smul_measure, smul_eq_mul]

#print axioms raw_middle_exact_scalar_height_law
#print axioms raw_middle_scalar_tilted_integral
end ConditionalSpectralAudit.FourierHarmonic
