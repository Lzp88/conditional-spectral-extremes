import IntegratedErrorScales
import HarmonicFineGeometry
import UniformEntropyGap

/-! Uniform 1+o(1) integrated middle moment on the manuscript's actual
fine scales. The only count restriction used is its fine-count upper bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Real BigOperators ENNReal Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ReservoirScale ArithmeticArcs

theorem actual_integrated_moment_on_scales (pmin P α Kmax ρ₀ ρ u₂ u₃ : Real)
    (hpP : pmin ≤ P) (hα : 0 < α) (hαp : α < pmin) (hα1 : α ≤ 1)
    (hKmax : 0 ≤ Kmax) (hρ₀ : 0 ≤ ρ₀) (hρ : ρ₀ < ρ) (hρ1 : ρ < 1)
    (hu₂ : 0 ≤ u₂) (huα : 1 < u₂*α) (hu₃ : 1 < u₃)
    (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar)
    (hrlarge : u₂+u₃+ρ*p.A₀ < p.rStar) :
    ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop,
      ∀ (s K : Real) (q : Nat → Nat), pmin ≤ s → s ≤ P → 0 ≤ K → K ≤ Kmax →
      K*entropyCost s ≤ ρ₀ →
      (∀ i < count p n, (q i : Real) ≤ K*omega p n) →
      (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s (fineBlockLo p n) (fineBlockHi p n) q (count p n) t) ∂haar) ≤
        ENNReal.ofReal (1+ε) := by
  obtain ⟨C, hC, hactual⟩ := actual_integrated_harmonic_bound pmin P α hpP hα hαp hα1
  intro ε hε
  have herr := (integrated_error_envelope_tendsto_one u₂ u₃ α p.rStar ρ p.A₀ C Kmax huα hu₃ hrlarge).eventually
    (gt_mem_nhds (by linarith : (1 : Real) < 1+ε))
  have hωlim := omega_tendsto_atTop p hA
  filter_upwards [herr, eventually_harmonic_fine_geometry p hA hr,
    eventually_fine_scale_geometry p hA hr, eventually_aStar_le_L,
    L_tendsto_atTop.eventually_ge_atTop 1,
    hωlim.eventually_ge_atTop (12*Kmax/(ρ-ρ₀)),
    hωlim.eventually_ge_atTop (Real.log 2/(1-ρ))] with n hen hgeom hscales haL hL hωlarge hωgeom
  intro s K q hsp hsP hK hKK hgap hq
  have hω : 0 < omega p n := hgeom.1
  have hcount : 0 < count p n := hscales.2.2.2.1
  have hsumwidth : (count p n : Real)*omega p n=aStar n-r p n := by
    unfold omega
    exact mul_div_cancel₀ _ (by exact_mod_cast hcount.ne')
  have hrn : 0 ≤ r p n := (Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)).trans hscales.2.2.1
  have hd : 0 ≤ aStar n-r p n := by
    rw [← hsumwidth]
    exact mul_nonneg (Nat.cast_nonneg _) hω.le
  have hQ : (∑ i ∈ Finset.range (count p n), (q i : Real)) ≤ Kmax*L n := by
    have hh := Finset.sum_le_sum (s := Finset.range (count p n)) (fun i hi => hq i (Finset.mem_range.mp hi))
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at hh
    have he : (count p n : Real)*(K*omega p n)=K*(aStar n-r p n) := by
      rw [← hsumwidth]
      ring
    rw [he] at hh
    exact hh.trans (mul_le_mul hKK (by linarith : aStar n-r p n ≤ L n) hd hKmax)
  have hlarge : 12*K ≤ (ρ-ρ₀)*omega p n := by
    have hh := (div_le_iff₀ (by linarith : 0 < ρ-ρ₀)).1 hωlarge
    nlinarith
  have hegeom : Real.exp (-(1-ρ)*omega p n) ≤ 1/2 := by
    have hh := (div_le_iff₀ (by linarith : 0 < 1-ρ)).1 hωgeom
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real)<2)]; norm_num
  obtain ⟨hR, _, _⟩ := integration_cutoff_bounds (L n) u₂ hL hu₂
  have hb := hactual s (r p n) (u₃*ell n) (omega p n) K ρ₀ ρ
    (integrationFrequencyCutoff (L n) u₂) (count p n) (fineBlockLo p n) (fineBlockHi p n) q
    hsp hsP hR hω hK hρ₀ hgap hlarge hegeom (fun i hi =>
      ⟨(hgeom.2 i).1, (hgeom.2 i).2.1, (hgeom.2 i).2.2.1, (hgeom.2 i).2.2.2, hq i hi⟩)
  have hnorm := integrated_normalizer_error_bound (L n) u₂ u₃ α C Kmax
    (∑ i ∈ Finset.range (count p n), (q i : Real)) hL hu₂ hα.le hC.le hKmax hQ
  have hbad := integrated_bad_arc_error_bound (L n) u₂ u₃ p.rStar ρ p.A₀ (omega p n)
    hL hu₂ (by linarith) hscales.2.2.2.2.2.1
  have hbound : Real.exp ((∑ i ∈ Finset.range (count p n), (q i : Real))*
      (C*((integrationFrequencyCutoff (L n) u₂ : Real)^(-α)+Real.exp (-(u₃*ell n)))))*
      (1+12*(integrationFrequencyCutoff (L n) u₂ : Real)*Real.exp (-(r p n)+u₃*ell n+ρ*omega p n)) ≤
      integratedErrorEnvelope (L n) u₂ u₃ α p.rStar ρ p.A₀ C Kmax := by
    change Real.exp _*(1+_) ≤ Real.exp _*(1+_)
    apply mul_le_mul (Real.exp_le_exp.mpr hnorm) (add_le_add le_rfl ?_)
      (by positivity) (Real.exp_pos _).le
    simpa only [r, ell, neg_mul] using hbad
  exact hb.trans (ENNReal.ofReal_le_ofReal (hbound.trans hen.le))

#print axioms actual_integrated_moment_on_scales
end ConditionalSpectralAudit.FourierHarmonic
