import RawPathFirstMoment
import ProductNormalizerError

/-! The actual moment scale μ_L and the complete product-normalizer error. -/
noncomputable section
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.CoarseBoxes

theorem countPrefix_eq_fine_sum (q : Nat → Nat) (m : Nat) :
    FineScales.countPrefix q m = ∑ i : Fin m, q (i.val+1) :=
  (Fin.sum_univ_eq_sum_range (fun i => q (i+1)) m).symm

def pathMomentScale (p : FineScales.Parameters) (n : Nat) (κ : Real) (q : Nat → Nat) : Real :=
  Real.exp (-criticalPoint κ*terminalHeight p n κ q) *
    logSineA (criticalPoint κ)^(FineScales.countPrefix q (FineScales.count p n))

theorem pathMomentScale_pos (p : FineScales.Parameters) (n : Nat) (κ : Real)
    (hκ : 0 < κ) (q : Nat → Nat) : 0 < pathMomentScale p n κ q := by
  unfold pathMomentScale
  exact mul_pos (Real.exp_pos _) (pow_pos (logSineA_pos _ (by linarith [criticalPoint_pos hκ])) _)

theorem pathMomentScale_exact (p : FineScales.Parameters) (n : Nat) (κ : Real)
    (hκ : 0 < κ) (q : Nat → Nat) :
    pathMomentScale p n κ q = Real.exp (-FineScales.aStar n+FineScales.r p n) := by
  have hs := criticalPoint_pos hκ
  rw [pathMomentScale, logSineA_eq_exp_lambda _ (by linarith), ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold terminalHeight
  field_simp
  ring

theorem fine_normalizer_product_ratio {m : Nat} (d : Nat) (A : Real) (b : Fin m → Real)
    (q : Nat → Nat) :
    (∏ i, b i^q (i.val+1))/A^(d*FineScales.countPrefix q m) =
      ∏ i, b i^q (i.val+1)/A^(d*q (i.val+1)) := by
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum,
    countPrefix_eq_fine_sum]

theorem fine_normalizer_product_relative_error {m : Nat} (d : Nat) (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (lo hi q : Nat → Nat) (ε : Real) (hε : 0 ≤ ε)
    (he : ∀ i : Fin m,
      |harmonicTiltNormalizer s t (lo i) (hi i)^q (i.val+1)/logSineA s^(d*q (i.val+1))-1| ≤ ε) :
    |(∏ i : Fin m, harmonicTiltNormalizer s t (lo i) (hi i)^q (i.val+1))/
      logSineA s^(d*FineScales.countPrefix q m)-1| ≤ m*ε*Real.exp (m*ε) := by
  rw [fine_normalizer_product_ratio]
  exact finite_product_relative_error _ ε hε he

#print axioms pathMomentScale_exact
#print axioms fine_normalizer_product_relative_error
end ConditionalSpectralAudit.FourierHarmonic
