import ActualCouplingEnergy
import ActualPoissonMaximum
import CoarseReferenceComparison
import CoarseCountEvents
import NaturalMultinomialEvents

/-! The two actual coarse Regular conditions under the true multinomial
reference distribution. Constants precede every choice of scale parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale FineScales

def finalRegularMaximumConstant (B : ℝ) : ℝ := regularMaximumConstant B+1
def finalRegularEnergyConstant (B : ℝ) : ℝ := 2*(regularEnergyConstant B+1)

theorem finalRegularMaximumConstant_pos (B : ℝ) : 0 < finalRegularMaximumConstant B := by
  unfold finalRegularMaximumConstant regularMaximumConstant
  positivity

theorem finalRegularEnergyConstant_pos (B : ℝ) : 0 < finalRegularEnergyConstant B := by
  unfold finalRegularEnergyConstant regularEnergyConstant
  positivity

theorem reference_coarse_energy_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬ CoarseEnergyEvent p n ((k:ℝ)/L n) (finalRegularEnergyConstant B)
          (naturalCountVector c)) < ε := by
  have hε2 : 0 < ε/2 := by positivity
  have hBG : Tendsto (fun n : ℕ => (groupNumber p n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (groupNumber_tendsto_atTop p hA hr hD)
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    actual_poisson_environment_energy_tendsto p hA hr hD ha haB (ε/2) hε2,
    actual_coupling_energy_tendsto p hA hr hD ha haB _ hBG (ε/2) hε2] with n hd hPoi hCouple
  intro k hak hkB
  have hh := reference_coarse_energy_comparison p n k hd.probNonneg hd.probSum hd.basePos hd.enoughBlocks
    (fun j => zero_lt_one.trans_le (hd.widthOne j)) (regularEnergyConstant B)
  have hp := hPoi hd.probNonneg k hak hkB
  have hc := hCouple hd.basePos hd.enoughBlocks hd.probNonneg hd.probSum k hak hkB
  have hprob : (naturalMultinomialPMF (fineReferenceProbabilities p n) hd.probNonneg hd.probSum k).toMeasure.real
      {Y | 2*(regularEnergyConstant B+1)*(groupNumber p n : ℝ) <
        ∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n ((k:ℝ)/L n) j Y)^2} < ε := by linarith
  rw [naturalMultinomial_probability] at hprob
  simpa only [CoarseEnergyEvent, finalRegularEnergyConstant, not_le] using hprob

theorem reference_coarse_max_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬ CoarseMaximumEvent p n ((k:ℝ)/L n) (finalRegularMaximumConstant B)
          (naturalCountVector c)) < ε := by
  classical
  have hε2 : 0 < ε/2 := by positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (ell n)) atTop atTop :=
    Real.tendsto_log_atTop.comp ell_tendsto_atTop
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    actual_poisson_environment_max_tendsto p hA hr hD ha haB (ε/2) hε2,
    actual_coupling_energy_tendsto p hA hr hD ha haB _ hlog (ε/2) hε2,
    hlog.eventually_ge_atTop 0] with n hd hPoi hCouple hln
  intro k hak hkB
  have hh := reference_coarse_max_comparison p n k hd.probNonneg hd.probSum hd.basePos hd.enoughBlocks
    (fun j => zero_lt_one.trans_le (hd.widthOne j)) (regularMaximumConstant B) (Real.log (ell n)) hln
  have hp := hPoi hd.probNonneg k hak hkB
  have hc := hCouple hd.basePos hd.enoughBlocks hd.probNonneg hd.probSum k hak hkB
  have hprob : (naturalMultinomialPMF (fineReferenceProbabilities p n) hd.probNonneg hd.probSum k).toMeasure.real
      {Y | ∃ j : Fin (groupNumber p n), (regularMaximumConstant B+1)*Real.sqrt (Real.log (ell n)) <
        coarseCountEnvironment p n ((k:ℝ)/L n) j Y} < ε := by linarith
  rw [naturalMultinomial_probability] at hprob
  simpa only [CoarseMaximumEvent, finalRegularMaximumConstant, not_forall, not_le] using hprob

#print axioms finalRegularMaximumConstant_pos
#print axioms finalRegularEnergyConstant_pos
#print axioms reference_coarse_energy_failure_tendsto
#print axioms reference_coarse_max_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
