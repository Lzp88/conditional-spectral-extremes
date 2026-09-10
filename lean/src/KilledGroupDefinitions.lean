import BridgeLowerBound
import BoxAlgebra

/-! The actual coarse-group kernel killed at prescribed fine endpoints.
The kernel retains the q-1 dimensional endpoint integral. The deterministic
chord condition gives an event inclusion, so it never assumes a killed
kernel estimate or a favorable endpoint probability. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def killedGroupEvent {ι : Type*} (q : ℕ) (times : ι → ℕ)
    (barrier : ι → ℝ) (x : ℝ) : Set (Fin q → ℝ) :=
  {y | ∀ i, x + FiniteWalk.partialSum (times i) y ≤ barrier i}

def killedGroupKernel {ι : Type*} (s : ℝ) (n : ℕ) (times : ι → ℕ)
    (barrier : ι → ℝ) (x x' : ℝ) : ℝ :=
  (pointwiseBridge (tiltedDensity s) n (x'-x)
    (killedGroupEvent (n+1) times barrier x)).toReal

theorem killedGroupEvent_measurable {ι : Type*} [Countable ι]
    (q : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ) :
    MeasurableSet (killedGroupEvent q times barrier x) := by
  simp only [killedGroupEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le _ measurable_const
  unfold FiniteWalk.partialSum
  fun_prop

theorem bridgeTube_subset_killedGroup {ι : Type*} (q : ℕ)
    (times : ι → ℕ) (htimes : ∀ i, times i ≤ q)
    (barrier : ι → ℝ) (x x' R : ℝ)
    (hgap : ∀ i, x + (times i : ℝ)/(q : ℝ)*(x'-x) + R ≤ barrier i) :
    bridgeTube q (x'-x) R ⊆ killedGroupEvent q times barrier x := by
  intro y hy i
  have hh := hy (times i) (htimes i)
  have hupper := (abs_le.mp hh).2
  have hg := hgap i
  change x + FiniteWalk.partialSum (times i) y ≤ barrier i
  linarith

theorem pointwiseBridge_tilted_ne_top (s : ℝ) (hs : -1 < s)
    (n : ℕ) (hn : 2 ≤ n) (d : ℝ) (E : Set (Fin (n+1) → ℝ)) :
    pointwiseBridge (tiltedDensity s) n d E ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ pointwiseBridge (tiltedDensity s) n d univ :=
      pointwiseBridge_mono _ _ _ (subset_univ _)
    _ = ENNReal.ofReal (tiltedDensityPower s (n+1) d) :=
      pointwiseBridge_tilted_eq_power s hs n hn d

theorem tubeBridge_le_killedGroupKernel {ι : Type*} (s : ℝ) (hs : -1 < s)
    (n : ℕ) (hn : 2 ≤ n) (times : ι → ℕ) (htimes : ∀ i, times i ≤ n+1)
    (barrier : ι → ℝ) (x x' R : ℝ)
    (hgap : ∀ i, x + (times i : ℝ)/((n+1 : ℕ) : ℝ)*(x'-x) + R ≤ barrier i) :
    (tubeBridge s n (x'-x) R).toReal ≤ killedGroupKernel s n times barrier x x' := by
  apply ENNReal.toReal_mono (pointwiseBridge_tilted_ne_top s hs n hn (x'-x) _)
  exact pointwiseBridge_mono _ _ _
    (bridgeTube_subset_killedGroup (n+1) times htimes barrier x x' R hgap)

theorem killedGroupKernel_nonneg {ι : Type*} (s : ℝ) (n : ℕ) (times : ι → ℕ)
    (barrier : ι → ℝ) (x x' : ℝ) :
    0 ≤ killedGroupKernel s n times barrier x x' := ENNReal.toReal_nonneg

theorem discrepancy_interpolation_bound (a H t q κ E c : ℝ)
    (hH : 0 < H) (hc : 0 < c) (ha : 0 ≤ a) (haH : a ≤ H)
    (hq : c*H ≤ q) (hE : 0 ≤ E)
    (hi : |t-κ*a| ≤ E*Real.sqrt H)
    (hend : |q-κ*H| ≤ E*Real.sqrt H) :
    |a-(t/q)*H| ≤ (2/c)*E*Real.sqrt H := by
  have hqpos : 0 < q := lt_of_lt_of_le (mul_pos hc hH) hq
  have hid := ConditionalSpectralAudit.BoxAlgebra.discrepancy_interpolation
    a H t q κ (t-κ*a) (q-κ*H) hqpos.ne' (by ring) (by ring)
  rw [hid, abs_div, abs_of_pos hqpos]
  apply (div_le_iff₀ hqpos).2
  have hnum : |a*(q-κ*H)-H*(t-κ*a)| ≤ 2*H*(E*Real.sqrt H) := by
    calc
      _ ≤ |a*(q-κ*H)|+|H*(t-κ*a)| := abs_sub _ _
      _ = a*|q-κ*H|+H*|t-κ*a| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos hH]
      _ ≤ a*(E*Real.sqrt H)+H*(E*Real.sqrt H) := by gcongr
      _ ≤ 2*H*(E*Real.sqrt H) := by
        have := mul_le_mul_of_nonneg_right haH (mul_nonneg hE (Real.sqrt_nonneg H))
        nlinarith
  apply hnum.trans
  have hq' : H ≤ q/c := (le_div_iff₀ hc).2 (by nlinarith [hq])
  have hh := mul_le_mul_of_nonneg_right hq'
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (mul_nonneg hE (Real.sqrt_nonneg H)))
  convert hh using 1 <;> ring

theorem frontier_chord_gap_lower (a₀ S₀ a H t q lam s γ₀ γ₁ e₀ e₁ κ E c G R : ℝ)
    (hs : 0 < s) (hH : 0 < H) (hc : 0 < c)
    (ha : 0 ≤ a) (haH : a ≤ H) (ht : 0 ≤ t) (htq : t ≤ q)
    (hq : c*H ≤ q) (hE : 0 ≤ E)
    (hi : |t-κ*a| ≤ E*Real.sqrt H) (hend : |q-κ*H| ≤ E*Real.sqrt H)
    (hg₀ : 2*G+R+(2/c)*E*Real.sqrt H/s ≤ γ₀-e₀)
    (hg₁ : 2*G+R+(2/c)*E*Real.sqrt H/s ≤ γ₁-e₁) :
    (1-t/q)*ConditionalSpectralAudit.BoxAlgebra.boxPoint a₀ lam S₀ s γ₀ e₀ +
      (t/q)*ConditionalSpectralAudit.BoxAlgebra.boxPoint (a₀+H) lam (S₀+q) s γ₁ e₁ + R ≤
        ConditionalSpectralAudit.BoxAlgebra.frontier (a₀+a) lam (S₀+t) s - 2*G := by
  have hqpos : 0 < q := lt_of_lt_of_le (mul_pos hc hH) hq
  have hf : 0 ≤ t/q := div_nonneg ht hqpos.le
  have hf1 : t/q ≤ 1 := (div_le_one hqpos).2 htq
  have hdis := discrepancy_interpolation_bound a H t q κ E c hH hc ha haH hq hE hi hend
  have hdiv : -(2/c*E*Real.sqrt H/s) ≤ (a-(t/q)*H)/s := by
    have hh := (abs_le.mp hdis).1
    have := div_le_div_of_nonneg_right hh hs.le
    simpa only [neg_div] using this
  have hc₀ := mul_le_mul_of_nonneg_left hg₀ (sub_nonneg.mpr hf1)
  have hc₁ := mul_le_mul_of_nonneg_left hg₁ hf
  have hh := ConditionalSpectralAudit.BoxAlgebra.chord_gap
    a₀ S₀ a H t q lam s γ₀ γ₁ e₀ e₁ hs.ne' hqpos.ne'
  nlinarith

#print axioms killedGroupEvent_measurable
#print axioms bridgeTube_subset_killedGroup
#print axioms pointwiseBridge_tilted_ne_top
#print axioms tubeBridge_le_killedGroupKernel
#print axioms killedGroupKernel_nonneg
#print axioms discrepancy_interpolation_bound
#print axioms frontier_chord_gap_lower

end ConditionalSpectralExtremes
