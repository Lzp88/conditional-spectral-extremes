import UniformNoiseDensity

/-! Exact finite products of actual probability densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set

namespace ConditionalSpectralAudit.FourierHarmonic

theorem independent_density_product {m : Nat} (f : Fin m → Real → Real)
    (hf : ∀ i, Integrable (f i)) (hfn : ∀ i x, 0 ≤ f i x) (h1 : ∀ i, ∫ x, f i x = 1) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : Fin m → Real => ∏ i, ENNReal.ofReal (f i (x i))) := by
  classical
  let _ (i : Fin m) := probability_of_real_density (hf i) (hfn i) (h1 i)
  apply Measure.pi_eq
  intro s hs
  let g : Fin m → Real → Real := fun i => (s i).indicator (f i)
  have hg (i : Fin m) : Integrable (g i) := (hf i).indicator (hs i)
  have hgn (i : Fin m) (x : Real) : 0 ≤ g i x := indicator_nonneg (fun y _ => hfn i y) x
  have hp := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure Real)) hg
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he : (univ.pi s).indicator (fun x => ∏ i, ENNReal.ofReal (f i (x i))) =
      fun x => ENNReal.ofReal (∏ i, g i (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [indicator_of_mem hx, ENNReal.ofReal_prod_of_nonneg (fun i _ => hgn i (x i))]
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      exact (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      have hex : ∃ i, x i ∉ s i := by simpa only [mem_univ_pi, not_forall] using hx
      obtain ⟨i,hi⟩ := hex
      have hz : (∏ j, g j (x j))=0 := Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)
      rw [hz, ENNReal.ofReal_zero]
  rw [he]
  dsimp only
  rw [volume_pi, ← ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hgn i (x i)))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hgn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hg i) (Filter.Eventually.of_forall (hgn i))]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s i <;> simp [g, hx]

theorem independent_density_product_real {m : Nat} (f : Fin m → Real → Real)
    (hf : ∀ i, Integrable (f i)) (hfn : ∀ i x, 0 ≤ f i x) (h1 : ∀ i, ∫ x, f i x = 1) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : Fin m → Real => ENNReal.ofReal (∏ i, f i (x i))) := by
  rw [independent_density_product f hf hfn h1]
  congr 1
  funext x
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hfn i (x i))).symm

#print axioms independent_density_product_real
end ConditionalSpectralAudit.FourierHarmonic
