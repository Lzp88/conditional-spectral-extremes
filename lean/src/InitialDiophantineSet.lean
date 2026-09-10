import ArithmeticBadSets
import IntegratedErrorScales

/-! The literal initial Diophantine set and the vanishing measure of its
complement, with the same rounded frequency cutoff used in smoothing. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Real Topology ENNReal
namespace ConditionalSpectralAudit.ArithmeticArcs
open FourierHarmonic ConditionalSpectralExtremes.ReservoirScale

def initialDiophantineSet (x u₂ u₃ rStar : Real) : Set Torus :=
  (badOne (integrationFrequencyCutoff x u₂) (Real.exp ((-rStar+u₃)*Real.log x)))ᶜ

theorem initialDiophantineSet_measurable (x u₂ u₃ rStar : Real) :
    MeasurableSet (initialDiophantineSet x u₂ u₃ rStar) := (badOne_measurable _ _).compl

theorem initialDiophantineSet_mem (x u₂ u₃ rStar : Real) (t : Torus) :
    t ∈ initialDiophantineSet x u₂ u₃ rStar ↔
      ∀ j : Int, |(j : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) → j ≠ 0 →
        Real.exp ((-rStar+u₃)*Real.log x) ≤ ‖j • t‖ :=
  not_mem_badOne _ _ t

theorem initialDiophantineSet_compl_measure (x u₂ u₃ rStar : Real) (hx : 1 ≤ x) (hu₂ : 0 ≤ u₂) :
    haar (initialDiophantineSet x u₂ u₃ rStar)ᶜ ≤ ENNReal.ofReal (12*x^(u₂+u₃-rStar)) := by
  have hp : 0 < x := by linarith
  obtain ⟨hR,_,hRu⟩ := integration_cutoff_bounds x u₂ hx hu₂
  have hm := badOne_measure_le_six (integrationFrequencyCutoff x u₂) hR
    (Real.exp ((-rStar+u₃)*Real.log x)) (Real.exp_pos _).le
  simp only [initialDiophantineSet, compl_compl]
  apply hm.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    6*(integrationFrequencyCutoff x u₂ : Real)*Real.exp ((-rStar+u₃)*Real.log x) ≤
        6*(2*x^u₂)*Real.exp ((-rStar+u₃)*Real.log x) := by gcongr
    _ = 12*x^(u₂+u₃-rStar) := by
      rw [exp_log_scale x _ hp,
        show u₂+u₃-rStar=u₂+(-rStar+u₃) by ring,
        Real.rpow_add hp u₂ (-rStar+u₃)]
      ring

theorem initialDiophantineSet_compl_eventually_small (u₂ u₃ rStar : Real)
    (hu₂ : 0 ≤ u₂) (hr : u₂+u₃ < rStar) (ε : Real) (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, haar (initialDiophantineSet (L n) u₂ u₃ rStar)ᶜ ≤ ENNReal.ofReal ε := by
  have ht : Tendsto (fun n : Nat => 12*(L n)^(u₂+u₃-rStar)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by linarith : 0 < -(u₂+u₃-rStar))).comp L_tendsto_atTop).const_mul 12
    simpa only [Function.comp_def, neg_neg, mul_zero] using hh
  filter_upwards [L_tendsto_atTop.eventually_ge_atTop 1, ht.eventually (gt_mem_nhds hε)] with n hL hn
  exact (initialDiophantineSet_compl_measure (L n) u₂ u₃ rStar hL hu₂).trans
    (ENNReal.ofReal_le_ofReal hn.le)

#print axioms initialDiophantineSet_compl_measure
#print axioms initialDiophantineSet_compl_eventually_small
end ConditionalSpectralAudit.ArithmeticArcs
