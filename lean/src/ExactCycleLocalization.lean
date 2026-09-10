import ShortReferenceHarmonicEquality
import UniformFullShortLocalization
import ShortReferenceLocalizationReduction

/-! The manuscript's main theorem, with its original finite conditional
configuration law and deterministic center. Every analytic, probabilistic,
and sampling input in the reduction is instantiated by a proved theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace ConditionalSpectralExtremes
open FineScales Reservoir ReservoirScale BlockCounts
open ConditionalSpectralAudit.FourierHarmonic

theorem actual_reference_short_localization {a B : Real} (ha : 0 < a) (haB : a ≤ B) :
    ReferenceShortLocalization a B := by
  obtain ⟨η,D₀,hη,hD₀,hchoose⟩ := uniform_full_short_harmonic_localization ha haB
    (finalRegularMaximumConstant B) (finalRegularEnergyConstant B) (6*B)
    (finalRegularMaximumConstant_pos B).le (finalRegularEnergyConstant_pos B).le
    (by have hB := ha.trans_le haB; positivity)
  refine ⟨η,D₀,hη,hD₀,?_⟩
  intro A₀ hA
  obtain ⟨rStar,C,hr,hC,hloc⟩ := hchoose A₀ hA
  refine ⟨rStar,C,hr,hC,?_⟩
  intro ε hε
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  filter_upwards [hloc ε hε,eventually_fine_scale_geometry p hA hr,
    eventually_full_short_sampling_probability p hA hr,
    cutoff_tendsto_atTop.eventually_gt_atTop 0,eventually_four_cutoff_le_n,
    ell_tendsto_atTop.eventually_gt_atTop 0] with n hlocn hgeo hsampling hb hbn hell
  intro k hak hkB hkn q hreg hq0 hqsum _hmass
  have hω : 0 < omega p n := by
    have hh : 0 < p.A₀*ell n/2 := by positivity
    exact hh.trans_le hgeo.2.2.2.2.1
  have hm : 0 < count p n := hgeo.2.2.2.1
  have hcut : cutoff n ≤ n := by omega
  have hH : ∀ i : Fin (count p n+1), 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j := by
    intro i
    rw [fineFiberWeight_sum p n i hω hm hb hcut]
    cases i using Fin.cases with
    | zero => exact hsampling.1
    | succ i => exact hsampling.2.1 i i.isLt
  have hq : ∀ i : Fin (count p n+1), q i ≤ n := by
    intro i
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (hqsum.trans hkn)
  have hlow : (q 0 : Real) ≤ (6*B)*rStar*ell n := by
    simpa only [r,mul_assoc] using hq0
  have hh := hlocn ((k : Real)/L n) ⟨hak,hkB⟩ q hreg hlow
  rw [← actual_short_reference_harmonic_failure_eq p n k q C hq hω hm hb hcut hH] at hh
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hh

theorem exact_cycle_localization : ExactCycleLocalization := by
  apply exactCycleLocalization_of_reference_short_localization
  intro a B ha haB
  exact actual_reference_short_localization ha haB.le

#print axioms actual_reference_short_localization
#print axioms exact_cycle_localization
end ConditionalSpectralExtremes
