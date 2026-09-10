import RawMomentBounds
import MomentIntegralBounds
import PathComparisonError
import NearClassSeparation

/-! The actual mean of Z_D, uniformly for every measurable subset of the good angles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath FineScales ArithmeticArcs

def FineMomentData (p : Parameters) (n : Nat) (q : Nat → Nat) (x : Real) : Prop :=
  0 ≤ omega p n ∧ ∀ i < count p n, (q (i+1) : Real) ≤ x ∧
    0 < fineBlockLo p n i ∧ 1 ≤ harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) ∧
    Real.exp (coordinate p n i) ≤ fineBlockLo p n i

def pathIntegralScale (p : Parameters) (n : Nat) (κ G δ : Real) (q : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) : Real :=
  AddCircle.haarAddCircle.real D * pathMomentScale p n κ q *
    (referencePathMass p n κ G q (fineSmoothingNoise δ (count p n))).toReal

def farPathPairs (p : Parameters) (n : Nat) (x u₂ u₃ : Real)
    (D : Set (AddCircle (1 : Real))) : Set (AddCircle (1 : Real) × AddCircle (1 : Real)) :=
  (D ×ˢ D) ∩ (badPair (integrationFrequencyCutoff x u₂) (Real.exp (-r p n+u₃*Real.log x)))ᶜ

theorem farPathPairs_measurable (p : Parameters) (n : Nat) (x u₂ u₃ : Real)
    (D : Set (AddCircle (1 : Real))) (hD : MeasurableSet D) :
    MeasurableSet (farPathPairs p n x u₂ u₃ D) :=
  (hD.prod hD).inter (badPair_measurable _ _).compl

theorem good_pair_separated_all_fine (p : Parameters) (n R i : Nat) (Δ : Real)
    (hω : 0 ≤ omega p n) (t u : Torus) (ht : (t,u) ∉ badPair R (Real.exp (-r p n+Δ))) :
    ∀ j : Int × Int, (|(j.1 : Real)| ≤ (R : Real) ∧ |(j.2 : Real)| ≤ (R : Real)) → j ≠ 0 →
      Real.exp (-coordinate p n i+Δ) ≤ ‖j.1 • t+j.2 • u‖ := by
  intro j hj hj0
  have he := (not_mem_badPair R _ (t,u)).mp ht j hj hj0
  apply le_trans (Real.exp_le_exp.mpr ?_) he
  have hh : r p n ≤ coordinate p n i := by
    unfold coordinate
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hω)
  linarith

theorem actual_integrated_first_moment_lower (p : Parameters) (n : Nat)
    (κ G pmin P J u₁ u₂ u₃ x ε : Real) (hκ : 0 < κ) (hp : 0 < pmin)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1One pmin P J u₁ u₂ u₃ x)
    (q : Nat → Nat) (hdata : FineMomentData p n q x)
    (D : Set (AddCircle (1 : Real))) (hD : MeasurableSet D)
    (hgood : D ⊆ (badOne (integrationFrequencyCutoff x u₂) (Real.exp (-r p n+u₃*Real.log x)))ᶜ)
    (herror : pathComparisonError (count p n) x J ≤ ε*
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal) :
    pathIntegralScale p n κ G (x^(-10 : Real)) q D*(1-ε) ≤
      ∫ z, (rawPathIntegral p n κ G (x^(-10 : Real)) q D z).toReal
        ∂harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun j => q (j+1)) (count p n) := by
  have hδ : 0 < x^(-10 : Real) := by positivity
  have hH (i : Nat) (hi : i < count p n) : 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) :=
    lt_of_lt_of_le zero_lt_one (hdata.2 i hi).2.2.1
  have hpoint (t : AddCircle (1 : Real)) (ht : t ∈ D) := actual_first_moment_comparison
    p n κ G pmin P J u₁ u₂ u₃ x hκ hp hsp hsP hx heps hpoly q (fineBlockLo p n) (fineBlockHi p n)
    (coordinate p n) t (fun i hi => (hdata.2 i hi).1) (fun i hi => (hdata.2 i hi).2.1)
    (fun i hi => (hdata.2 i hi).2.2.1) (fun i hi => (hdata.2 i hi).2.2.2)
    (fun i _ => good_one_separated_all_fine p n _ i _ hdata.1 t (hgood ht))
  have hlower := setIntegral_lower_of_normalized_error AddCircle.haarAddCircle D hD
    (rawFirstMoment p n κ G (x^(-10 : Real)) q (fineBlockLo p n) (fineBlockHi p n))
    (rawFirstMoment_integrable p n κ G (x^(-10 : Real)) hκ hδ q (fineBlockLo p n) (fineBlockHi p n) hH _)
    (pathMomentScale p n κ q)
    (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal
    (pathComparisonError (count p n) x J) (pathMomentScale_pos p n κ hκ q) hpoint
  rw [rawPathIntegral_first_moment_real p n κ G (x^(-10 : Real)) hκ hδ]
  apply le_trans ?_ hlower
  unfold pathIntegralScale
  have hscalar := mul_le_mul_of_nonneg_left
    (show (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal*(1-ε) ≤
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal-
        pathComparisonError (count p n) x J by nlinarith)
    (show 0 ≤ AddCircle.haarAddCircle.real D * pathMomentScale p n κ q from
      mul_nonneg measureReal_nonneg (pathMomentScale_pos p n κ hκ q).le)
  simpa only [mul_assoc] using hscalar

#print axioms actual_integrated_first_moment_lower
end ConditionalSpectralAudit.FourierHarmonic
