import RawHarmonicSampling

/-! Exact almost-sure support of the actual harmonic length samples. -/
noncomputable section
open MeasureTheory Set Filter
namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted

theorem normalizedLaw_ae_of_forall {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset ι) (w : ι → Real) (X : ι → Ω) (P : Ω → Prop)
    (hP : ∀ i ∈ S, P (X i)) : ∀ᵐ x ∂normalizedLaw S w X, P x := by
  classical
  rw [ae_iff]
  unfold normalizedLaw
  rw [Measure.smul_apply]
  have hz : weightedLaw S w X {x | ¬P x}=0 := by
    rw [weightedLaw, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    simp [Measure.smul_apply, Measure.dirac_apply, hP i hi]
  rw [hz]
  simp

theorem harmonicLengthLaw_support (m n : Nat) :
    ∀ᵐ j ∂harmonicLengthLaw m n, m ≤ j ∧ j < n :=
  normalizedLaw_ae_of_forall _ _ _ _ (fun _j hj => Finset.mem_Ico.mp hj)

theorem harmonicBlockSampleLaw_support (m n q : Nat) :
    ∀ᵐ x ∂harmonicBlockSampleLaw m n q, ∀ v : Fin q, m ≤ x v ∧ x v < n := by
  unfold harmonicBlockSampleLaw
  apply ae_all_iff.mpr
  intro v
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin q => harmonicLengthLaw m n) (i := v)).eventually
    (harmonicLengthLaw_support m n)

theorem harmonicMiddleSampleLaw_support (lo hi q : Nat → Nat) (m : Nat) :
    ∀ᵐ x ∂harmonicMiddleSampleLaw lo hi q m, ∀ (i : Fin m) (v : Fin (q i)),
      lo i ≤ x i v ∧ x i v < hi i := by
  unfold harmonicMiddleSampleLaw
  apply ae_all_iff.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun i : Fin m => harmonicBlockSampleLaw (lo i) (hi i) (q i)) (i := i)).eventually
    (harmonicBlockSampleLaw_support (lo i) (hi i) (q i))

theorem harmonicMiddleSampleLaw_positive_bounded (lo hi q : Nat → Nat) (m b : Nat)
    (hlo : ∀ i < m, 0 < lo i) (hhi : ∀ i < m, hi i ≤ b+1) :
    ∀ᵐ x ∂harmonicMiddleSampleLaw lo hi q m, ∀ (i : Fin m) (v : Fin (q i)),
      0 < x i v ∧ x i v ≤ b := by
  filter_upwards [harmonicMiddleSampleLaw_support lo hi q m] with x hx
  intro i v
  have hh := hx i v
  have h1 := hlo i i.isLt
  have h2 := hhi i i.isLt
  omega

#print axioms harmonicMiddleSampleLaw_support
#print axioms harmonicMiddleSampleLaw_positive_bounded
end ConditionalSpectralAudit.FourierHarmonic
