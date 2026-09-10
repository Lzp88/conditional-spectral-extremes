import FineScaleAsymptotics
import UniformCriticalParameters
import LambdaMomentUpper

/-! Exact comparison of the actual variational center with the short
center after deleting at most O(log log n) long cycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes
open ReservoirScale FineScales

theorem center_eq_critical_formula {n k : Nat} (hn : 1 < n) (hk : 0 < k) :
    center n k=(L n+(k : Real)*lambda (criticalPoint ((k : Real)/L n)))/
      criticalPoint ((k : Real)/L n) := by
  have hL : 0 < L n := Real.log_pos (by exact_mod_cast hn)
  have hκ : 0 < (k : Real)/L n := div_pos (by exact_mod_cast hk) hL
  rw [center_eq_speed hn hk]
  change L n*speed ((k : Real)/L n)=_
  rw [speed_eq_min_cost hκ]
  unfold variationalCost L
  unfold L at hL
  field_simp [hL.ne']

theorem eventually_log_cutoff_gap :
    ∀ᶠ n : Nat in atTop, 0 ≤ L n-aStar n ∧ L n-aStar n ≤ 5*ell n := by
  have habs := log_cutoff_error_tendsto_zero.abs
  simp only [abs_zero] at habs
  have he := habs.eventually (gt_mem_nhds (by norm_num : (0 : Real)<1))
  filter_upwards [he, eventually_aStar_le_L, ell_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with n herror hAL hell hn
  rw [log_unroundedCutoff hn] at herror
  change |aStar n-(L n-4*ell n)|<1 at herror
  have hh := (abs_lt.mp herror).1
  exact ⟨by linarith,by linarith⟩

theorem critical_center_difference (L₀ a k l s : Real) (hs : s ≠ 0) :
    (L₀+k*lambda s)/s-(a+(k-l)*lambda s)/s = (L₀-a)/s+l*(lambda s/s) := by
  field_simp
  ring

theorem uniform_short_center_comparison {a B C : Real} (ha : 0 < a) (_haB : a ≤ B) (hC : 0 ≤ C) :
    ∀ᶠ n : Nat in atTop, ∀ k l : Nat, a ≤ (k : Real)/L n → (k : Real)/L n ≤ B →
      l ≤ k → (l : Real) ≤ C*ell n →
      |center n k-(aStar n+lambda (criticalPoint ((k : Real)/L n))*(k-l : Nat))/
        criticalPoint ((k : Real)/L n)| ≤ (5/criticalPoint B+C*Real.log 2)*ell n := by
  filter_upwards [eventually_log_cutoff_gap, ell_tendsto_atTop.eventually_ge_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0, eventually_ge_atTop 2] with n hgap hell hL hn
  intro k l hklo hkhi hlk hl
  have hk : 0 < k := by
    have hh : 0 < (k : Real)/L n := ha.trans_le hklo
    have hp : 0 < (k : Real) := (div_pos_iff.mp hh).resolve_right (by intros h; linarith [h.2]) |>.1
    exact_mod_cast hp
  let s := criticalPoint ((k : Real)/L n)
  have hs := criticalPoint_compact_bounds ha hklo hkhi
  have hsp : 0 < s := hs.1.trans_le hs.2.1
  have hlam : 0 ≤ lambda s := lambda_nonneg (by linarith)
  have hlamu : lambda s/s ≤ Real.log 2 := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith [lambda_le_s_log_two s hsp.le]
  rw [center_eq_critical_formula (by omega) hk, Nat.cast_sub hlk]
  change |(L n+(k : Real)*lambda s)/s-(aStar n+lambda s*((k : Real)-l))/s| ≤ _
  rw [show aStar n+lambda s*((k : Real)-l)=aStar n+((k : Real)-l)*lambda s by ring,
    critical_center_difference _ _ _ _ _ hsp.ne']
  have hg : 0 ≤ (L n-aStar n)/s+(l : Real)*(lambda s/s) :=
    add_nonneg (div_nonneg hgap.1 hsp.le) (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hlam hsp.le))
  rw [abs_of_nonneg hg]
  have h1 : (L n-aStar n)/s ≤ 5*ell n/criticalPoint B :=
    (div_le_div_of_nonneg_right hgap.2 hsp.le).trans
      (div_le_div_of_nonneg_left (by positivity) hs.1 hs.2.1)
  have h2 : (l : Real)*(lambda s/s) ≤ C*ell n*Real.log 2 :=
    mul_le_mul hl hlamu (div_nonneg hlam hsp.le) (mul_nonneg hC hell)
  calc
    _ ≤ 5*ell n/criticalPoint B+C*ell n*Real.log 2 := add_le_add h1 h2
    _ = (5/criticalPoint B+C*Real.log 2)*ell n := by ring

#print axioms center_eq_critical_formula
#print axioms uniform_short_center_comparison
end ConditionalSpectralExtremes
