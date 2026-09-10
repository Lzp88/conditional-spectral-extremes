import OrderedBlockPartialSums
import PathWeightDefinitions

/-! The manuscript's reference fine path is exactly the block-sum image
of one ordered iid sequence, with all prefix sums preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup
open FineScales KernelPath

theorem blockSums_measurePreserving (m : Nat) (q : Nat → Nat) (μ : Measure Real) [IsProbabilityMeasure μ] :
    MeasurePreserving (blockSums m q)
      (Measure.pi (fun i : Fin m => Measure.pi (fun _v : Fin (q i) => μ)))
      (Measure.pi (fun i : Fin m => (Measure.pi (fun _v : Fin (q i) => μ)).map (fun x => ∑ v, x v))) :=
  measurePreserving_pi _ _ (fun _i => ⟨by fun_prop, rfl⟩)

def orderedFineSums (m : Nat) (q : Nat → Nat) (x : Fin (blockPrefix q m) → Real) : Fin m → Real :=
  blockSums m q ((orderedBlockSamplesEquiv m q Real).symm x)

theorem orderedFineSums_measurePreserving (m : Nat) (q : Nat → Nat) (μ : Measure Real) [IsProbabilityMeasure μ] :
    MeasurePreserving (orderedFineSums m q) (Measure.pi (fun _k : Fin (blockPrefix q m) => μ))
      (Measure.pi (fun i : Fin m => (Measure.pi (fun _v : Fin (q i) => μ)).map (fun x => ∑ v, x v))) :=
  (blockSums_measurePreserving m q μ).comp (orderedBlockSamplesEquiv_symm_measurePreserving m q μ)

theorem orderedFineSums_partialSum (m k : Nat) (q : Nat → Nat) (hk : k ≤ m)
    (x : Fin (blockPrefix q m) → Real) :
    FiniteWalk.partialSum k (orderedFineSums m q x) = FiniteWalk.partialSum (blockPrefix q k) x := by
  rw [orderedFineSums, blockSums_partialSum m k q hk, MeasurableEquiv.apply_symm_apply]

theorem actual_reference_fine_law_from_iid (s : Real) (hs : -1 < s) (m : Nat) (q : Nat → Nat) :
    MeasurePreserving (orderedFineSums m (fun i => q (i+1)))
      (tiltedLogSineProduct s (countPrefix q m)) (referenceFineLaw s m q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  exact orderedFineSums_measurePreserving m (fun i => q (i+1)) (tiltedLogSineLaw s)

theorem actual_reference_fine_prefix (m k : Nat) (q : Nat → Nat) (hk : k ≤ m)
    (x : Fin (countPrefix q m) → Real) :
    FiniteWalk.partialSum k (orderedFineSums m (fun i => q (i+1)) x) =
      FiniteWalk.partialSum (countPrefix q k) x :=
  orderedFineSums_partialSum m k (fun i => q (i+1)) hk x

#print axioms actual_reference_fine_law_from_iid
#print axioms actual_reference_fine_prefix
end ConditionalSpectralExtremes.IIDRegroup
