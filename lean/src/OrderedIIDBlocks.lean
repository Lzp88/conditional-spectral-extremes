import IIDProductRegrouping
import OrderedBlockIndices

/-! Measure-preserving ordered concatenation of the actual independent
variables. The inverse evaluates at prefix length plus the within-block index. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
namespace ConditionalSpectralExtremes.IIDRegroup

def orderedBlockSamplesEquiv (m : Nat) (q : Nat → Nat) (Ω : Type*) [MeasurableSpace Ω] :
    ((i : Fin m) → Fin (q i) → Ω) ≃ᵐ (Fin (blockPrefix q m) → Ω) :=
  (MeasurableEquiv.piCurry (fun (i : Fin m) (_v : Fin (q i)) => Ω)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _k : Fin (blockPrefix q m) => Ω) (orderedBlockEquiv m q))

theorem orderedBlockSamplesEquiv_symm_apply (m : Nat) (q : Nat → Nat) {Ω : Type*} [MeasurableSpace Ω]
    (x : Fin (blockPrefix q m) → Ω) (i : Fin m) (v : Fin (q i)) :
    (orderedBlockSamplesEquiv m q Ω).symm x i v = x (orderedBlockEquiv m q ⟨i,v⟩) := rfl

theorem orderedBlockSamplesEquiv_measurePreserving (m : Nat) (q : Nat → Nat)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (orderedBlockSamplesEquiv m q Ω)
      (Measure.pi (fun i : Fin m => Measure.pi (fun _v : Fin (q i) => μ)))
      (Measure.pi (fun _k : Fin (blockPrefix q m) => μ)) :=
  (measurePreserving_piCongrLeft (fun _k : Fin (blockPrefix q m) => μ) (orderedBlockEquiv m q)).comp
    (measurePreserving_sigmaUncurry μ)

theorem orderedBlockSamplesEquiv_symm_measurePreserving (m : Nat) (q : Nat → Nat)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (orderedBlockSamplesEquiv m q Ω).symm
      (Measure.pi (fun _k : Fin (blockPrefix q m) => μ))
      (Measure.pi (fun i : Fin m => Measure.pi (fun _v : Fin (q i) => μ))) :=
  MeasurePreserving.symm (orderedBlockSamplesEquiv m q Ω) (orderedBlockSamplesEquiv_measurePreserving m q μ)

#print axioms orderedBlockSamplesEquiv_measurePreserving
#print axioms orderedBlockSamplesEquiv_symm_measurePreserving
end ConditionalSpectralExtremes.IIDRegroup
