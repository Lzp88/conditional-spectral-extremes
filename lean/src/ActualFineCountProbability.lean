import FineCountProbability
import ActualCountEventComparison

/-! First regularity condition under the literal fixed-cycle profile law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale FineScales

theorem actual_fine_count_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) {a B η : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      conditionalProbability n k (fun s => ¬FineCountEvent p n ((k : ℝ)/L n) η
        (profileBlockCounts (fineCategoryBlock p n) s)) < ε := by
  have he : 0 < ε/2 := by positivity
  filter_upwards [reference_fine_count_failure_tendsto p hA hr ha haB hη hAlarge (ε/2) he,
    actual_and_multinomial_event_comparison ha haB (ε/2) he] with n href hcmp
  intro k hak hkB
  have ht := href k hak hkB
  have hc := hcmp k hak hkB (count p n) (fineCategoryBlock p n)
    (fun q => ¬FineCountEvent p n ((k : ℝ)/L n) η q)
  have hd : |conditionalProbability n k (fun s => ¬FineCountEvent p n ((k : ℝ)/L n) η
      (profileBlockCounts (fineCategoryBlock p n) s))-
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬FineCountEvent p n ((k : ℝ)/L n) η (fun j => (c.val j).val))| < ε/2 := by
    simpa only [fineReferenceProbabilities, show fineHarmonicMass p n =
      shortBlockHarmonicMass n (cutoff n) (fineCategoryBlock p n) from rfl] using hc
  linarith [(abs_lt.mp hd).2]

#print axioms actual_fine_count_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
