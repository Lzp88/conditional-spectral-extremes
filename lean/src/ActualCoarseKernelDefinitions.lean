import CoarseGroupKernelGeometry
import KilledGroupLaw

/-! The actual group kernel of Lemma boxes. The free dimension is q_j-1
and the barriers run over the literal fine endpoints in that group. -/

noncomputable section
open scoped ENNReal
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

def actualCoarseKernel (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (x x' : ℝ) : ℝ :=
  killedGroupKernel (criticalPoint κ) (groupSamples p n q j-1)
    (fun i : Fin (groupBlocks p n j+1) => groupTime p n q j i.val)
    (fun i : Fin (groupBlocks p n j+1) => groupBarrier p n κ G q j i.val) x x'

def actualCoarseKernelENN (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (x x' : ℝ) : ℝ≥0∞ :=
  killedGroupKernelENN (criticalPoint κ) (groupSamples p n q j-1)
    (fun i : Fin (groupBlocks p n j+1) => groupTime p n q j i.val)
    (fun i : Fin (groupBlocks p n j+1) => groupBarrier p n κ G q j i.val) x x'

#print axioms actualCoarseKernel
#print axioms actualCoarseKernelENN

end ConditionalSpectralExtremes.CoarseBoxes
