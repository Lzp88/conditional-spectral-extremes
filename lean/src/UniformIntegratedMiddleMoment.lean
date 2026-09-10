import ActualIntegratedAsymptotic

/-! The integrated middle-moment lemma at the actual critical parameter,
uniformly over the manuscript's regular count environments. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Real BigOperators ENNReal Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ArithmeticArcs

theorem uniform_integrated_middle_moment {a B : Real} (ha : 0 < a) (haB : a ≤ B) :
    ∃ η : Real, 0 < η ∧ ∀ A₀ : Real, 0 < A₀ → ∃ r₀ : Real, 0 < r₀ ∧
      ∀ rStar D₀ : Real, r₀ ≤ rStar → ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop,
        ∀ (κ K_E C_E : Real) (q : Nat → Nat), κ ∈ Icc a B →
        Regular ⟨A₀,rStar,D₀⟩ n κ η K_E C_E q →
        (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio (criticalPoint κ)
          (fineBlockLo ⟨A₀,rStar,D₀⟩ n) (fineBlockHi ⟨A₀,rStar,D₀⟩ n)
          (fun i => q (i+1)) (count ⟨A₀,rStar,D₀⟩ n) t) ∂haar) ≤ ENNReal.ofReal (1+ε) := by
  obtain ⟨η,ρ₀,hη,hρ₀,hρ₀1,hgap⟩ := actual_uniform_entropy_gap ha haB
  have hB : 0 < B := ha.trans_le haB
  let smin := criticalPoint B
  let smax := criticalPoint a
  have hsmin : 0 < smin := criticalPoint_pos hB
  have hsorder : smin ≤ smax := criticalPoint_strictAntiOn.antitoneOn ha hB haB
  let α := min (smin/2) (1/2)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαp : α < smin := (min_le_left _ _).trans_lt (by linarith)
  have hα1 : α ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let ρ := (ρ₀+1)/2
  have hρ : ρ₀ < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hρpos : 0 < ρ := hρ₀.trans hρ
  let u₂ := 2/α
  have hu₂ : 0 < u₂ := by dsimp [u₂]; positivity
  have huα : 1 < u₂*α := by dsimp [u₂]; rw [div_mul_cancel₀ _ hα.ne']; norm_num
  refine ⟨η,hη,?_⟩
  intro A₀ hA
  refine ⟨u₂+4+A₀, by positivity, ?_⟩
  intro rStar D₀ hrStar ε hε
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  have hr : 0 < p.rStar := by dsimp [p]; linarith
  have hrlarge : u₂+2+ρ*p.A₀ < p.rStar := by
    dsimp [p]
    nlinarith
  have hh := actual_integrated_moment_on_scales smin smax α (B+η) ρ₀ ρ u₂ 2
    hsorder hα hαp hα1 (by positivity) hρ₀.le hρ hρ1 hu₂.le huα (by norm_num)
    p hA hr hrlarge ε hε
  filter_upwards [hh] with n hn
  intro κ K_E C_E q hκ hreg
  have hs := criticalPoint_compact_bounds ha hκ.1 hκ.2
  exact hn (criticalPoint κ) (κ+η) (fun i => q (i+1)) hs.2.1 hs.2.2
    (by have := ha.trans_le hκ.1; positivity) (by linarith [hκ.2]) (hgap κ hκ)
    (fun i hi => (hreg.1 i (Finset.mem_range.mpr hi)).2)

#print axioms uniform_integrated_middle_moment
end ConditionalSpectralAudit.FourierHarmonic
