import ActualCoarseRateBounds
import CoarsePoissonEnvironment
import CoarseGroupGrowth

/-! The actual Poisson coarse-count squared energy is regular with
probability tending to one. All constants depend only on the compact
k/log n interval, before the fixed scale parameters are chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal Topology

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirScale FineScales

def regularRateConstant (B : ℝ) : ℝ := 1+2*B
def regularFourthConstant (B : ℝ) : ℝ := 128+6144*Real.exp 1*(regularRateConstant B)^2
def regularEnergyConstant (B : ℝ) : ℝ := 2*(129+6144*Real.exp 1*(regularRateConstant B)^2)
def regularMaximumConstant (B : ℝ) : ℝ := 8*Real.sqrt (regularRateConstant B)

theorem actual_poisson_environment_energy_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
        (Measure.pi (fun i => poissonMeasure (finePoissonRates p n k hp i))).real
          {X | regularEnergyConstant B*(groupNumber p n : ℝ) ≤
            ∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n ((k : ℝ)/L n) j X)^2} < ε := by
  let C := regularRateConstant B
  have hB : 0 < B := ha.trans_le haB
  have hC : 0 ≤ C := by dsimp only [C, regularRateConstant]; positivity
  have hBG : Tendsto (fun n : ℕ => (groupNumber p n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (groupNumber_tendsto_atTop p hA hr hD)
  have ht : Tendsto (fun n : ℕ => (128+6144*Real.exp 1*C^2)/
      ((129+6144*Real.exp 1*C^2)^2*(groupNumber p n : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (128+6144*Real.exp 1*C^2)/(129+6144*Real.exp 1*C^2)^2) atTop
      (𝓝 ((128+6144*Real.exp 1*C^2)/(129+6144*Real.exp 1*C^2)^2))).div_atTop hBG
    simpa only [div_mul_eq_div_div] using hh
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    (groupNumber_tendsto_atTop p hA hr hD).eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds hε)] with n hd hg hsmall
  intro hp k hak hkB
  have hH (j : Fin (groupNumber p n)) : 0 < groupWidth p n j := zero_lt_one.trans_le (hd.widthOne j)
  have hUpper (j : Fin (groupNumber p n)) :
      (∑ i, (finePoissonRates p n k hp (coarseCountIndex p n hd.basePos hd.enoughBlocks j i) : ℝ)) ≤ C*groupWidth p n j := by
    apply (hd.rateBounds k hak hkB j).2.1.trans
    dsimp only [C, regularRateConstant]
    nlinarith [hH j]
  have hh := coarsePoisson_environment_energy_tail p n hd.basePos hd.enoughBlocks (by omega)
    ((k : ℝ)/L n) C hC (finePoissonRates p n k hp) hH
    (fun j => (hd.rateBounds k hak hkB j).1) hUpper (fun j => (hd.rateBounds k hak hkB j).2.2)
  apply lt_of_le_of_lt ?_ hsmall
  simpa only [regularEnergyConstant, C] using hh

#print axioms actual_poisson_environment_energy_tendsto

end ConditionalSpectralExtremes.BlockCounts
