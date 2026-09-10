import ConditionalProbabilityEvents
import ActualPolynomialInsertion
import FinalCenterComparison

/-! Exact finite closing inequalities. The analytic short localization
and long-count tails remain separate inputs until their actual proofs are connected. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes
open ReservoirScale FineScales

def actualShortCenter (n k : Nat) (c : Configuration n) : Real :=
  (aStar n+lambda (criticalPoint ((k : Real)/L n))*
    (k-cycleCount (longConfiguration (cutoff n) c) : Nat))/criticalPoint ((k : Real)/L n)

theorem longConfiguration_count_le {n k : Nat} (b : Nat) (c : Configuration n) (hc : Valid k c) :
    cycleCount (longConfiguration b c) ≤ k := by
  rw [← hc.2]
  unfold cycleCount
  apply Finset.sum_le_sum
  intro j _
  simp only [longConfiguration]
  split <;> simp

theorem final_localization_pointwise (ell₀ M Mshort m mshort Cs Cc Cl : Real)
    (hell : 1 ≤ ell₀) (hCl : 0 ≤ Cl)
    (hshort : |Mshort-mshort| ≤ Cs*ell₀) (hcenter : |m-mshort| ≤ Cc*ell₀)
    (hinslow : -ell₀-Real.log 2 ≤ M-Mshort)
    (hinsup : M-Mshort ≤ Cl*ell₀*Real.log 2) :
    |M-m| ≤ (Cs+Cc+1+(1+Cl)*Real.log 2)*ell₀ := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht := abs_sub_le M Mshort m
  have hc := abs_sub_le Mshort mshort m
  rw [abs_sub_comm mshort m] at hc
  have hd : |M-Mshort| ≤ (1+(1+Cl)*Real.log 2)*ell₀ := by
    apply abs_le.mpr
    constructor
    · have h1 := mul_le_mul_of_nonneg_right hell hlog
      have h2 := mul_nonneg (mul_nonneg hCl (show 0 ≤ ell₀ by linarith)) hlog
      nlinarith
    · have h1 := mul_nonneg (show 0 ≤ ell₀ by linarith) (show 0 ≤ 1+Real.log 2 by linarith)
      nlinarith
  linarith

theorem actual_localization_failure_decomposition {a B Cs Cl : Real}
    (ha : 0 < a) (haB : a ≤ B) (hCl : 0 ≤ Cl) :
    ∀ᶠ n : Nat in atTop, ∀ k : Nat, a ≤ (k : Real)/L n → (k : Real)/L n ≤ B →
      conditionalProbability n k (fun c =>
        |maximumLogModulus c-center n k| >
          (Cs+(5/criticalPoint B+Cl*Real.log 2)+1+(1+Cl)*Real.log 2)*ell n) ≤
      conditionalProbability n k (fun c =>
        |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > Cs*ell n)+
      conditionalProbability n k (fun c => (cycleCount (longConfiguration (cutoff n) c) : Real)>Cl*ell n)+
      conditionalProbability n k (fun c => ell n+Real.log 2 ≤
        maximumLogModulus (shortConfiguration (cutoff n) c)-maximumLogModulus c) := by
  filter_upwards [uniform_short_center_comparison ha haB hCl,
    ell_tendsto_atTop.eventually_ge_atTop 1] with n hcenter hell
  intro k hklo hkhi
  apply (conditionalProbability_mono_valid _
    (fun c =>
      |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > Cs*ell n ∨
      (cycleCount (longConfiguration (cutoff n) c) : Real)>Cl*ell n ∨
      ell n+Real.log 2 ≤ maximumLogModulus (shortConfiguration (cutoff n) c)-maximumLogModulus c)
    ?_).trans (conditionalProbability_union_three_le _ _ _)
  intro c hc hbad
  by_contra hnone
  push Not at hnone
  have hcnt := longConfiguration_count_le (cutoff n) c hc
  have hcen := hcenter k (cycleCount (longConfiguration (cutoff n) c)) hklo hkhi hcnt hnone.2.1
  change |center n k-actualShortCenter n k c| ≤ _ at hcen
  have hins := (actual_short_long_insertion (cutoff n) c).2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hupper := hins.trans (mul_le_mul_of_nonneg_right hnone.2.1 hlog)
  have hh := final_localization_pointwise (ell n) (maximumLogModulus c)
    (maximumLogModulus (shortConfiguration (cutoff n) c)) (center n k)
    (actualShortCenter n k c) Cs (5/criticalPoint B+Cl*Real.log 2) Cl hell hCl
    hnone.1 hcen (by linarith [hnone.2.2]) hupper
  exact (not_lt_of_ge hh) hbad

#print axioms actual_localization_failure_decomposition
end ConditionalSpectralExtremes
