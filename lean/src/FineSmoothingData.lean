import HarmonicFineGeometry

/-! Literal fine blocks satisfy every sample-size and endpoint hypothesis of smoothing. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ReservoirScale

theorem eventually_regular_fine_smoothing_data (p : Parameters) (hA : 0 < p.A₀)
    (hr : 0 < p.rStar) (B η : Real) (hB : 0 < B) (hη : 0 ≤ η) :
    ∀ᶠ n : Nat in atTop, ∀ (κ K_E C_E : Real) (q : Nat → Nat), κ ≤ B →
      Regular p n κ η K_E C_E q →
      0 < count p n ∧ (count p n : Real) ≤ L n ∧ 0 < omega p n ∧
      ∀ i < count p n, (q (i+1) : Real) ≤ L n ∧
        0 < fineBlockLo p n i ∧ 1 ≤ harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) ∧
        Real.exp (coordinate p n i) ≤ fineBlockLo p n i := by
  have ht : Tendsto (fun n : Nat => ((B+η)*p.A₀)*(ell n/L n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ell_div_L_tendsto_zero.const_mul ((B+η)*p.A₀)
  filter_upwards [eventually_harmonic_fine_geometry p hA hr, eventually_fine_scale_geometry p hA hr,
    L_tendsto_atTop.eventually_gt_atTop 0, ht.eventually (gt_mem_nhds (by norm_num : (0 : Real)<1))]
    with n hgeo hscales hL hsmall
  intro κ K_E C_E q hκ hreg
  refine ⟨hscales.2.2.2.1,hscales.2.2.2.2.2.2,hgeo.1,?_⟩
  intro i hi
  have hbound : (B+η)*p.A₀*ell n ≤ L n := by
    have hh : ((B+η)*p.A₀*ell n)/L n ≤ 1 := by
      simpa only [mul_div_assoc] using hsmall.le
    simpa using (div_le_iff₀ hL).mp hh
  have hqi : (q (i+1) : Real) ≤ L n := by
    calc
      _ ≤ (κ+η)*omega p n := (hreg.1 i (Finset.mem_range.mpr hi)).2
      _ ≤ (B+η)*omega p n := mul_le_mul_of_nonneg_right (by linarith) hgeo.1.le
      _ ≤ (B+η)*(p.A₀*ell n) := mul_le_mul_of_nonneg_left hscales.2.2.2.2.2.1 (by linarith)
      _ ≤ L n := by nlinarith
  exact ⟨hqi,(hgeo.2 i).1,(hgeo.2 i).2.1,(hgeo.2 i).2.2.2⟩

#print axioms eventually_regular_fine_smoothing_data
end ConditionalSpectralAudit.FourierHarmonic
