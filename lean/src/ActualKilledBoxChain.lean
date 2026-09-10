import BoxChainSubprobability
import KilledGroupLaw

/-! Finiteness and integrated minorization for a chain of the actual
tilted log-sine killed kernels. Subprobability row bounds are proved
properties of those kernels and are not additional input assumptions. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def actualKilledBoxChain (s : ℝ) (B : ℕ) (free fine : Fin B → ℕ)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x₀ : ℝ) : ℝ≥0∞ :=
  boxChainIntegral B (fun j => killedGroupKernelENN s (free j) (times j) (barrier j)) lo hi x₀

theorem actualKilledBoxChain_le_one (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin B → ℕ) (hfree : ∀ j, 2 ≤ free j)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x₀ : ℝ) : actualKilledBoxChain s B free fine times barrier lo hi x₀ ≤ 1 := by
  apply boxChainIntegral_le_one
  · intro j
    exact killedGroupKernelENN_measurable s (free j) (times j) (barrier j)
  · intro j x x'
    exact pointwiseBridge_tilted_ne_top s hs (free j) (hfree j) (x'-x) _
  · intro j x
    exact killedGroupKernelENN_rowmass_le_one s hs (free j) (times j) (barrier j) x

theorem actualKilledBoxChain_ne_top (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin B → ℕ) (hfree : ∀ j, 2 ≤ free j)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x₀ : ℝ) : actualKilledBoxChain s B free fine times barrier lo hi x₀ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (actualKilledBoxChain_le_one s hs B free fine hfree times barrier lo hi x₀)

theorem actualKilledBoxChain_lower (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin B → ℕ) (hfree : ∀ j, 2 ≤ free j)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (hlohi : lo ≤ hi) (x₀ : ℝ) (l : Fin B → ℝ) (hl : ∀ j, 0 ≤ l j)
    (hminor : ∀ j : Fin B, ∀ x ∈ Icc (endpointPath B x₀ lo j.castSucc) (endpointPath B x₀ hi j.castSucc),
      ∀ x' ∈ Icc (lo j) (hi j), l j ≤ killedGroupKernel s (free j) (times j) (barrier j) x x') :
    (∏ j, l j)*(∏ j : Fin B, (hi j-lo j)) ≤ (actualKilledBoxChain s B free fine times barrier lo hi x₀).toReal := by
  apply boxChainIntegral_real_lower B _ lo hi x₀ l hlohi hl
    (actualKilledBoxChain_ne_top s hs B free fine hfree times barrier lo hi x₀)
  intro j x hx x' hx'
  rw [← killedGroupKernel_ofReal_eq s hs (free j) (hfree j) (times j) (barrier j) x x']
  exact ENNReal.ofReal_le_ofReal (hminor j x hx x' hx')

#print axioms actualKilledBoxChain_le_one
#print axioms actualKilledBoxChain_ne_top
#print axioms actualKilledBoxChain_lower

end ConditionalSpectralExtremes
