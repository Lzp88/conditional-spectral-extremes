import RawMiddleChangeMeasure
import PathWeightDefinitions

/-! The exact norm-power/log-height identity with every spectral root retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes
attribute [local instance] Classical.propDecidable

def rawMiddleRootFree {m : Nat} {q : Nat → Nat} (t : AddCircle (1 : Real))
    (x : (i : Fin m) → Fin (q i) → Nat) : Prop :=
  ∀ (i : Fin m) (v : Fin (q i)), ‖(1 : Complex)-fourier 1 (x i v • t)‖ ≠ 0

theorem raw_middle_factor_eq_exponential {m : Nat} {q : Nat → Nat}
    (s : Real) (hs : 0 < s) (t : AddCircle (1 : Real)) (x : (i : Fin m) → Fin (q i) → Nat) :
    rawHarmonicMiddleVectorFactor s (fun _ : Fin 1 => t) x =
      if rawMiddleRootFree t x then
        Real.exp (s*∑ i, rawHarmonicMiddleHeight (fun _ : Fin 1 => t) x i 0) else 0 := by
  classical
  by_cases hr : rawMiddleRootFree t x
  · rw [if_pos hr]
    have he (i : Fin m) (v : Fin (q i)) :
        ‖(1 : Complex)-fourier 1 (x i v • t)‖^s = Real.exp (s*logSine (x i v • t)) := by
      rw [Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hr i v)))]
      unfold logSine
      congr 1
      ring
    unfold rawHarmonicMiddleVectorFactor rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
    simp only [Fin.prod_univ_one]
    simp_rw [he, ← Real.exp_sum, ← Finset.mul_sum]
    rfl
  · rw [if_neg hr]
    obtain ⟨i,v,hz⟩ : ∃ (i : Fin m) (v : Fin (q i)), ‖(1 : Complex)-fourier 1 (x i v • t)‖ = 0 := by
      simpa only [rawMiddleRootFree, not_forall, not_not] using hr
    unfold rawHarmonicMiddleVectorFactor
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold rawHarmonicBlockVectorFactor
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [rawHarmonicVectorFactor, Fin.prod_univ_one, hz, Real.zero_rpow hs.ne']

theorem full_partialSum_eq_sum {m : Nat} (x : Fin m → Real) :
    FiniteWalk.partialSum m x = ∑ i, x i := by
  simp [FiniteWalk.partialSum, FiniteWalk.prefixIndices]

#print axioms raw_middle_factor_eq_exponential
end ConditionalSpectralAudit.FourierHarmonic
