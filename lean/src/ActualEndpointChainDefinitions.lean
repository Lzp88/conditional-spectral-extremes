import ActualCoarseKernelDefinitions
import CoarseEndpointBoxes
import FreshGroupBoxProbability

/-! The fully specified endpoint chain for the actual dyadic boxes.
Both the density integral and the fresh iid sampling expression are
given, so probability regrouping can target the same fixed object. -/

noncomputable section
open scoped ENNReal
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

def actualEndpointChain (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) : ℝ≥0∞ :=
  actualKilledBoxChain (criticalPoint κ) (groupNumber p n)
    (fun j => groupSamples p n q j.val-1) (fun j => groupBlocks p n j.val+1)
    (fun j i => groupTime p n q j.val i.val) (fun j i => groupBarrier p n κ G q j.val i.val)
    (fun j => endpointLower p n κ G B₀ q (j.val+1))
    (fun j => endpointUpper p n κ G B₀ q (j.val+1)) 0

def actualFreshBoxProbability (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) : ℝ≥0∞ :=
  freshGroupBoxProbability (criticalPoint κ) (groupNumber p n)
    (fun j => groupSamples p n q j.val-1) (fun j => groupBlocks p n j.val+1)
    (fun j i => groupTime p n q j.val i.val) (fun j i => groupBarrier p n κ G q j.val i.val)
    (fun j => endpointLower p n κ G B₀ q (j.val+1))
    (fun j => endpointUpper p n κ G B₀ q (j.val+1)) 0

theorem actualEndpointChain_eq_fresh (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hq : ∀ j < groupNumber p n, 3 ≤ groupSamples p n q j) :
    actualEndpointChain p n κ G B₀ q = actualFreshBoxProbability p n κ G B₀ q := by
  exact (freshGroupBoxProbability_eq_chain (criticalPoint κ) (by linarith [criticalPoint_pos hκ])
    (groupNumber p n) _ _ (fun j => by have hh := hq j.val j.isLt; omega) _ _ _ _ 0).symm

#print axioms actualEndpointChain_eq_fresh

end ConditionalSpectralExtremes.CoarseBoxes
