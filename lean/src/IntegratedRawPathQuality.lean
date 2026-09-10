import RawPathQuality

/-! The manuscript's actual Z_D, on the same raw sample space and with the same Z(t). -/
noncomputable section
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

def rawPathIntegral (p : ConditionalSpectralExtremes.FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (q : Nat → Nat) (D : Set (AddCircle (1 : Real)))
    (x : FineRawSample p n q) : ENNReal :=
  ∫⁻ t in D, rawPathQuality p n κ G δ q t x ∂AddCircle.haarAddCircle

theorem rawPathIntegral_measurable (p : ConditionalSpectralExtremes.FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (q : Nat → Nat) (D : Set (AddCircle (1 : Real))) :
    Measurable (rawPathIntegral p n κ G δ q D) := measurable_of_countable _

#print axioms rawPathIntegral_measurable
end ConditionalSpectralAudit.FourierHarmonic
