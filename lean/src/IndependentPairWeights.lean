import PairPathReferenceMass

/-! Independent paired product measures, for two possibly distinct path weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set WithLp
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

theorem independent_pair_weights {m : Nat} (μ ν : Fin m → Measure Real)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (W V : (Fin m → Real) → ENNReal) (hW : Measurable W) (hV : Measurable V) :
    (∫⁻ w, W (fun i => (ofLp (w i)).1)*V (fun i => (ofLp (w i)).2)
      ∂Measure.pi (fun i => ((μ i).prod (ν i)).map (toLp 2))) =
      (∫⁻ w, W w ∂Measure.pi μ)*(∫⁻ w, V w ∂Measure.pi ν) := by
  have ht : Measurable (toLp 2 : Real × Real → PairSpace) := by fun_prop
  have hp : Measurable (fun w : Fin m → Real × Real => fun i => toLp 2 (w i)) := by fun_prop
  have hw : Measurable (fun w : Fin m → PairSpace =>
      W (fun i => (ofLp (w i)).1)*V (fun i => (ofLp (w i)).2)) :=
    (hW.comp (by fun_prop)).mul (hV.comp (by fun_prop))
  rw [← Measure.pi_map_pi (fun _ => ht.aemeasurable), lintegral_map hw hp]
  have hm := measurePreserving_arrowProdEquivProdArrow Real Real (Fin m) μ ν
  calc
    _ = ∫⁻ w : (Fin m → Real) × (Fin m → Real), W w.1*V w.2 ∂(Measure.pi μ).prod (Measure.pi ν) := by
      convert! hm.lintegral_comp ((hW.comp measurable_fst).mul (hV.comp measurable_snd)) using 1
    _ = _ := lintegral_prod_mul hW.aemeasurable hV.aemeasurable

theorem pair_noise_path_integral (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (hδ : 0 < δ) (q : Nat → Nat) (w v : Fin (FineScales.count p n) → Real) :
    (∫⁻ ζ, pairPathWeight p n κ G q ((fun i => toLp 2 (w i,v i))+ζ)
      ∂Measure.pi (fun _ : Fin (FineScales.count p n) => pairUniformNoise δ)) =
      (∫⁻ ζ, pathWeight p n κ G q (w+ζ) ∂fineSmoothingNoise δ (FineScales.count p n)) *
      (∫⁻ ζ, pathWeight p n κ G q (v+ζ) ∂fineSmoothingNoise δ (FineScales.count p n)) := by
  let _ := tenUniformNoise_probability δ hδ
  have hW : Measurable (fun ζ => pathWeight p n κ G q (w+ζ)) :=
    (pathWeight_measurable p n κ G q).comp (by fun_prop)
  have hV : Measurable (fun ζ => pathWeight p n κ G q (v+ζ)) :=
    (pathWeight_measurable p n κ G q).comp (by fun_prop)
  convert! independent_pair_weights (fun _ : Fin (FineScales.count p n) => tenUniformNoise δ)
    (fun _ : Fin (FineScales.count p n) => tenUniformNoise δ) _ _ hW hV using 1

#print axioms pair_noise_path_integral
end ConditionalSpectralAudit.FourierHarmonic
