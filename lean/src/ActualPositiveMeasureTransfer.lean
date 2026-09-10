import ActualReservoirFlatness
import ConditionalReservoirTransfer
import ActualCoefficientComparison

/-! Actual reservoir transfer for arbitrary positive measure coefficients.
The measure space, event, and coefficient mass do not enter the error bound. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale Reservoir

def reservoirMeasureCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (n b l D : ℕ) (ν : Fin (D+1) → Measure Ω) : Measure Ω :=
  ∑ d, ENNReal.ofReal (reservoirCoefficient n b (n-d.val) l) • ν d

theorem actual_positive_measure_transfer {a B C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let ε := C*((ell n)⁻¹+(L n)^(-3 : ℤ))
      0 ≤ ε ∧ ε < 1 ∧ ∀ l : ℕ, a ≤ (l : ℝ)/T n → (l : ℝ)/T n ≤ B →
        0 < reservoirCoefficient n (cutoff n) n l ∧
        ∀ (Ω : Type*) [MeasurableSpace Ω] (D : ℕ) (ν : Fin (D+1) → Measure Ω),
          (D : ℝ) ≤ C₀*L n*cutoff n →
          ENNReal.ofReal ((1-ε)*reservoirCoefficient n (cutoff n) n l) • (∑ d, ν d) ≤
            reservoirMeasureCoefficient n (cutoff n) l D ν ∧
          reservoirMeasureCoefficient n (cutoff n) l D ν ≤
            ENNReal.ofReal ((1+ε)*reservoirCoefficient n (cutoff n) n l) • (∑ d, ν d) := by
  obtain ⟨C, hC, he⟩ := actual_reservoir_flatness ha haB hC₀
  have hsmall := (reservoir_flatness_error_tendsto_zero C).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, hC, ?_⟩
  filter_upwards [he, hsmall, ell_tendsto_atTop.eventually_gt_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0] with n hn hs hℓ hL
  dsimp only
  refine ⟨by positivity, hs, ?_⟩
  intro l hal hlB
  have hd0 : (0 : ℝ) ≤ C₀*L n*cutoff n := by positivity
  have hr := (hn 0 (by simpa using hd0) l hal hlB).1
  refine ⟨hr, ?_⟩
  intro Ω _ D ν hD
  have hweights (d : Fin (D+1)) :
      (1-C*((ell n)⁻¹+(L n)^(-3 : ℤ)))*reservoirCoefficient n (cutoff n) n l ≤
        reservoirCoefficient n (cutoff n) (n-d.val) l ∧
      reservoirCoefficient n (cutoff n) (n-d.val) l ≤
        (1+C*((ell n)⁻¹+(L n)^(-3 : ℤ)))*reservoirCoefficient n (cutoff n) n l := by
    have hd : (d.val : ℝ) ≤ C₀*L n*cutoff n :=
      (show (d.val : ℝ) ≤ D by exact_mod_cast (show d.val ≤ D by omega)).trans hD
    have he := abs_le.mp (hn d.val hd l hal hlB).2
    have hlo := (le_div_iff₀ hr).mp (show 1-C*((ell n)⁻¹+(L n)^(-3 : ℤ)) ≤
      reservoirCoefficient n (cutoff n) (n-d.val) l / reservoirCoefficient n (cutoff n) n l by linarith)
    have hup := (div_le_iff₀ hr).mp (show
      reservoirCoefficient n (cutoff n) (n-d.val) l / reservoirCoefficient n (cutoff n) n l ≤
        1+C*((ell n)⁻¹+(L n)^(-3 : ℤ)) by linarith)
    exact ⟨hlo, hup⟩
  constructor
  · unfold reservoirMeasureCoefficient
    rw [Finset.smul_sum]
    apply Finset.sum_le_sum
    intro d _ s
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hweights d).1)
      (zero_le : (0 : ENNReal) ≤ ν d s)
  · unfold reservoirMeasureCoefficient
    rw [Finset.smul_sum]
    apply Finset.sum_le_sum
    intro d _ s
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hweights d).2)
      (zero_le : (0 : ENNReal) ≤ ν d s)

#print axioms actual_positive_measure_transfer
end ConditionalSpectralExtremes.ReservoirAnalysis
