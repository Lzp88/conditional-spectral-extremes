import ReferencePairSmoothing

/-! The two-coordinate reference path weight is exactly p_L squared. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set WithLp
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

def pairPathWeight (p : FineScales.Parameters) (n : Nat) (κ G : Real) (q : Nat → Nat)
    (w : Fin (FineScales.count p n) → PairSpace) : ENNReal :=
  pathWeight p n κ G q (fun i => (ofLp (w i)).1) *
    pathWeight p n κ G q (fun i => (ofLp (w i)).2)

theorem pairPathWeight_measurable (p : FineScales.Parameters) (n : Nat) (κ G : Real) (q : Nat → Nat) :
    Measurable (pairPathWeight p n κ G q) := by
  unfold pairPathWeight
  exact ((pathWeight_measurable p n κ G q).comp (by fun_prop)).mul
    ((pathWeight_measurable p n κ G q).comp (by fun_prop))

theorem pairPathWeight_le_one (p : FineScales.Parameters) (n : Nat) (κ G : Real)
    (q : Nat → Nat) (hκ : 0 < κ) (w : Fin (FineScales.count p n) → PairSpace) :
    pairPathWeight p n κ G q w ≤ 1 := by
  unfold pairPathWeight
  simpa using mul_le_mul' (pathWeight_le_one p n κ G q hκ _) (pathWeight_le_one p n κ G q hκ _)

theorem independent_pair_path_integral {m : Nat} (μ : Fin m → Measure Real)
    [∀ i, IsProbabilityMeasure (μ i)] (W : (Fin m → Real) → ENNReal) (hW : Measurable W) :
    (∫⁻ w, W (fun i => (ofLp (w i)).1)*W (fun i => (ofLp (w i)).2)
      ∂Measure.pi (fun i => ((μ i).prod (μ i)).map (toLp 2))) =
      (∫⁻ w, W w ∂Measure.pi μ)^2 := by
  have ht : Measurable (toLp 2 : Real × Real → PairSpace) := by fun_prop
  have hp : Measurable (fun w : Fin m → Real × Real => fun i => toLp 2 (w i)) := by fun_prop
  have hw : Measurable (fun w : Fin m → PairSpace =>
      W (fun i => (ofLp (w i)).1)*W (fun i => (ofLp (w i)).2)) := by
    exact (hW.comp (by fun_prop)).mul (hW.comp (by fun_prop))
  rw [← Measure.pi_map_pi (fun _ => ht.aemeasurable), lintegral_map hw hp]
  have hm := measurePreserving_arrowProdEquivProdArrow Real Real (Fin m) μ μ
  calc
    _ = ∫⁻ w : (Fin m → Real) × (Fin m → Real), W w.1*W w.2 ∂(Measure.pi μ).prod (Measure.pi μ) := by
      convert! hm.lintegral_comp ((hW.comp measurable_fst).mul (hW.comp measurable_snd)) using 1
    _ = (∫⁻ w, W w ∂Measure.pi μ)*(∫⁻ w, W w ∂Measure.pi μ) :=
      lintegral_prod_mul hW.aemeasurable hW.aemeasurable
    _ = _ := (pow_two _).symm

theorem actual_reference_pair_path_mass (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat) :
    (∫⁻ w, pairPathWeight p n κ G q w ∂Measure.pi (fun i : Fin (FineScales.count p n) =>
      (pairVectorLaw (referenceVectorSumLaw (criticalPoint κ) 2 (q (i.val+1)))) ∗ pairUniformNoise δ)) =
      (referencePathMass p n κ G q (fineSmoothingNoise δ (FineScales.count p n)))^2 := by
  let m := FineScales.count p n
  let s := criticalPoint κ
  have hs : -1 < s := by dsimp only [s]; linarith [criticalPoint_pos hκ]
  let _ (i : Fin m) := referenceVectorSumLaw_probability s hs 1 (q (i.val+1))
  let _ (i : Fin m) := coordinateLaw_probability (referenceVectorSumLaw s 1 (q (i.val+1))) 0
  let _ := tenUniformNoise_probability δ hδ
  let _ := fineSmoothingNoise_probability δ hδ m
  simp_rw [reference_pair_smoothed_independent (criticalPoint κ) δ hs hδ]
  unfold pairPathWeight
  rw [independent_pair_path_integral _ _ (pathWeight_measurable p n κ G q),
    ← finite_pi_convolution]
  rw [referencePathMass_eq_smoothed_integral, referenceFineLaw_eq_coordinateProduct s hs]
  rfl

#print axioms actual_reference_pair_path_mass
end ConditionalSpectralAudit.FourierHarmonic
