import RawScalarTiltBridge
import RawPathQuality
import PairFinePathComparison

/-! Exact coupled two-point reweighting on the original harmonic sample space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set WithLp
namespace ConditionalSpectralAudit.FourierHarmonic

def rawMiddlePairHeight {m : Nat} {q : Nat → Nat} (t₁ t₂ : AddCircle (1 : Real))
    (x : (i : Fin m) → Fin (q i) → Nat) : Fin m → PairSpace :=
  fun i => pairVectorMap (rawHarmonicMiddleHeight ![t₁,t₂] x i)

def finePairTiltedLaw (s : Real) (t₁ t₂ : AddCircle (1 : Real)) (lo hi q : Nat → Nat) (m : Nat) :
    Measure (Fin m → PairSpace) := Measure.pi (fun i : Fin m =>
      pairVectorLaw (harmonicTiltSumLaw s ![t₁,t₂] (lo i) (hi i) (q (i.val+1))))

theorem raw_middle_exact_pair_height_law (s : Real) (t₁ t₂ : AddCircle (1 : Real))
    (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < m, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i), harmonicTiltWeight s ![t₁,t₂] j) :
    ((harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m).withDensity
      (fun x => ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s ![t₁,t₂] x))).map
        (rawMiddlePairHeight (q := fun j => q (j+1)) t₁ t₂) =
      ENNReal.ofReal (∏ i : Fin m, harmonicTiltNormalizer s ![t₁,t₂] (lo i) (hi i)^q (i.val+1)) •
        finePairTiltedLaw s t₁ t₂ lo hi q m := by
  let _ (i : Fin m) := harmonicTiltSumLaw_probability s ![t₁,t₂]
    (lo i) (hi i) (q (i.val+1)) (hW i i.isLt)
  have hm : Measurable (fun w : Fin m → Fin 2 → Real => fun i => pairVectorMap (w i)) := by
    exact measurable_pi_lambda _ (fun i => pairVectorMap_measurable.comp (measurable_pi_apply i))
  have hr : Measurable (@rawHarmonicMiddleHeight 2 m (fun j => q (j+1)) ![t₁,t₂]) :=
    measurable_of_countable _
  have he := congrArg (fun μ : Measure (Fin m → Fin 2 → Real) =>
    μ.map (fun w i => pairVectorMap (w i)))
    (raw_middle_exact_tilted_height_law s ![t₁,t₂] lo hi (fun j => q (j+1)) m hH hW)
  rw [Measure.map_map hm hr, Measure.map_smul] at he
  unfold harmonicMiddleTiltLaw at he
  rw [Measure.pi_map_pi (fun _ => pairVectorMap_measurable.aemeasurable)] at he
  exact he

theorem raw_middle_pair_tilted_integral (s : Real) (t₁ t₂ : AddCircle (1 : Real))
    (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < m, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i), harmonicTiltWeight s ![t₁,t₂] j)
    (φ : (Fin m → PairSpace) → ENNReal) (hφ : Measurable φ) :
    (∫⁻ x, ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s ![t₁,t₂] x) *
      φ (rawMiddlePairHeight (q := fun j => q (j+1)) t₁ t₂ x)
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m) =
      ENNReal.ofReal (∏ i : Fin m, harmonicTiltNormalizer s ![t₁,t₂] (lo i) (hi i)^q (i.val+1)) *
        ∫⁻ w, φ w ∂finePairTiltedLaw s t₁ t₂ lo hi q m := by
  have hr : Measurable (rawMiddlePairHeight (m := m) (q := fun j => q (j+1)) t₁ t₂) := measurable_of_countable _
  have hd : Measurable (fun x : (i : Fin m) → Fin (q (i.val+1)) → Nat =>
      ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) s ![t₁,t₂] x)) := measurable_of_countable _
  have he := lintegral_withDensity_eq_lintegral_mul
    (harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) m) hd (hφ.comp hr)
  simp only [Pi.mul_apply, Function.comp_def] at he
  rw [← he, ← lintegral_map hφ hr, raw_middle_exact_pair_height_law s t₁ t₂ lo hi q m hH hW,
    lintegral_smul_measure, smul_eq_mul]

#print axioms raw_middle_pair_tilted_integral
end ConditionalSpectralAudit.FourierHarmonic
