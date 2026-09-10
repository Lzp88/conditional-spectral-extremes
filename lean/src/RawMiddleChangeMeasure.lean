import RawHarmonicChangeMeasure

/-! All manuscript fine blocks, with the full product of their true normalizers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem rawHarmonicBlockVectorFactor_integrable {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) :
    Integrable (rawHarmonicBlockVectorFactor s t) (harmonicBlockSampleLaw m n q) := by
  have hf : Integrable (rawHarmonicVectorFactor s t) (harmonicLengthLaw m n) :=
    (weightedLaw_integrable_real _ _ _ _).smul_measure ENNReal.ofReal_ne_top
  exact Integrable.fintype_prod (fun _ => hf)

theorem rawHarmonicBlockVectorFactor_nonneg {d q : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (x : Fin q → Nat) :
    0 ≤ rawHarmonicBlockVectorFactor s t x := by
  unfold rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
  positivity

def rawHarmonicMiddleVectorFactor {d m : Nat} {q : Nat → Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (x : (i : Fin m) → Fin (q i) → Nat) : Real :=
  ∏ i, rawHarmonicBlockVectorFactor s t (x i)

def rawHarmonicMiddleHeight {d m : Nat} {q : Nat → Nat}
    (t : Fin d → AddCircle (1 : Real)) (x : (i : Fin m) → Fin (q i) → Nat) :
    Fin m → Fin d → Real := fun i => rawHarmonicBlockHeight t (x i)

def harmonicMiddleTiltLaw {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (lo hi q : Nat → Nat) (m : Nat) : Measure (Fin m → Fin d → Real) :=
  Measure.pi (fun i : Fin m => harmonicTiltSumLaw s t (lo i) (hi i) (q i))

theorem raw_middle_exact_tilted_height_law {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < m, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i), harmonicTiltWeight s t j) :
    ((harmonicMiddleSampleLaw lo hi q m).withDensity
      (fun x => ENNReal.ofReal (rawHarmonicMiddleVectorFactor s t x))).map (rawHarmonicMiddleHeight t) =
      ENNReal.ofReal (∏ i : Fin m, harmonicTiltNormalizer s t (lo i) (hi i)^q i) •
        harmonicMiddleTiltLaw s t lo hi q m := by
  let _ (i : Fin m) := harmonicTiltSumLaw_probability s t (lo i) (hi i) (q i) (hW i i.isLt)
  have hfi (i : Fin m) := rawHarmonicBlockVectorFactor_integrable s t (lo i) (hi i) (q i)
  have hfn (i : Fin m) := @rawHarmonicBlockVectorFactor_nonneg d (q i) s t
  let μ : (i : Fin m) → Measure (Fin (q i) → Nat) := fun i =>
    (harmonicBlockSampleLaw (lo i) (hi i) (q i)).withDensity
      (fun x => ENNReal.ofReal (rawHarmonicBlockVectorFactor s t x))
  let _ (i : Fin m) : IsFiniteMeasure (μ i) := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi i) (ae_of_all _ (hfn i))]
    exact ENNReal.ofReal_ne_top)
  have hm (i : Fin m) : Measurable (@rawHarmonicBlockHeight d (q i) t) := measurable_of_countable _
  unfold harmonicMiddleSampleLaw rawHarmonicMiddleVectorFactor rawHarmonicMiddleHeight
  rw [← finite_measure_density_product _ _ hfi hfn, Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [raw_block_exact_tilted_height_law s t _ _ _ (hH _ (Fin.isLt _)) (hW _ (Fin.isLt _))]
  rw [finite_pi_smul _ _ (fun _ => ENNReal.ofReal_ne_top)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun (i : Fin m) _ =>
    show 0 ≤ harmonicTiltNormalizer s t (lo i) (hi i)^q i from
      pow_nonneg (div_nonneg (hW i i.isLt).le (hH i i.isLt).le) _)]
  rfl

#print axioms raw_middle_exact_tilted_height_law
end ConditionalSpectralAudit.FourierHarmonic
