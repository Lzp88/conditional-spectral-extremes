import FullShortHarmonicLaw

/-! Literal low and fine harmonic blocks all have positive mass eventually. -/
noncomputable section
open MeasureTheory Filter
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales

theorem harmonicMass_one_lower {N : Nat} (hN : 2 ≤ N) : 1 ≤ harmonicMass 1 N := by
  unfold harmonicMass
  have hh := Finset.single_le_sum
    (f := fun j : Nat => (j : Real)⁻¹) (s := Finset.Ico 1 N)
    (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))
    (show 1 ∈ Finset.Ico 1 N by simp; omega)
  simpa only [Nat.cast_one,inv_one] using hh

theorem eventually_full_short_sampling_probability (p : Parameters) (hA : 0 < p.A₀)
    (hr : 0 < p.rStar) :
    ∀ᶠ n : Nat in atTop, 0 < harmonicMass 1 (fineBlockLo p n 0) ∧
      (∀ i < count p n, 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i)) ∧
      ∀ q : Nat → Nat, IsProbabilityMeasure (fullShortHarmonicLaw p n q) := by
  filter_upwards [eventually_harmonic_fine_geometry p hA hr,
    (r_tendsto_atTop p hr).eventually_ge_atTop (Real.log 2)] with n hgeo hrn
  have hex : (2 : Real) ≤ Real.exp (r p n) := by
    simpa only [Real.exp_log (by norm_num : (0 : Real)<2)] using Real.exp_le_exp.mpr hrn
  have helo : Real.exp (r p n) ≤ (fineBlockLo p n 0 : Real) := by
    simpa only [fineBlockLo,coordinate_zero] using exp_le_exponentialEndpoint (r p n)
  have hlo : 2 ≤ fineBlockLo p n 0 := by exact_mod_cast hex.trans helo
  have hlow := (by norm_num : (0 : Real)<1).trans_le (harmonicMass_one_lower hlo)
  have hfine : ∀ i < count p n, 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) :=
    fun i _ => (by norm_num : (0 : Real)<1).trans_le (hgeo.2 i).2.1
  exact ⟨hlow,hfine,fun q => fullShortHarmonicLaw_probability p n q hlow hfine⟩

#print axioms eventually_full_short_sampling_probability
end ConditionalSpectralAudit.FourierHarmonic
