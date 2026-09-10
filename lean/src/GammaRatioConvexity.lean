import Mathlib

/-! Strict convexity of log Gamma ratios, proved from Euler's actual limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes

def logStep (a x : ℝ) : ℝ := Real.log (x + a) - Real.log x

theorem logStep_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (logStep a) ((x + a)⁻¹ - x⁻¹) x := by
  have h := ((hasDerivAt_id x).add_const a).log (by positivity : x + a ≠ 0)
  simpa only [logStep, one_div, id_eq, Pi.sub_apply] using! h.sub (Real.hasDerivAt_log hx.ne')

theorem logStep_deriv2 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (deriv^[2] (logStep a)) x = (x ^ 2)⁻¹ - ((x + a) ^ 2)⁻¹ := by
  have he : deriv (logStep a) =ᶠ[𝓝 x] (fun y => (y + a)⁻¹ - y⁻¹) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (logStep_hasDerivAt ha hy).deriv
  have d1 := ((hasDerivAt_id x).add_const a).inv (by positivity : x + a ≠ 0)
  have d2 := (hasDerivAt_id x).inv hx.ne'
  change deriv (deriv (logStep a)) x = _
  rw [he.deriv_eq]
  have hd : HasDerivAt (fun y : ℝ => (y + a)⁻¹ - y⁻¹)
      (-1 / (x + a) ^ 2 - -1 / x ^ 2) x := by
    simpa only [id_eq, Pi.inv_apply, Pi.sub_apply] using! d1.sub d2
  rw [hd.deriv]
  ring

theorem logStep_strictConvexOn {a : ℝ} (ha : 0 < a) :
    StrictConvexOn ℝ (Ioi 0) (logStep a) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro x hx
    exact (logStep_hasDerivAt ha hx).continuousAt.continuousWithinAt
  · intro x hx
    change 0 < x at hx
    rw [logStep_deriv2 ha hx, sub_pos]
    exact inv_lt_inv₀ (by positivity) (by positivity) |>.2 (by nlinarith [show 0 < x from hx])

def logRatioTailSeq (a x : ℝ) (n : ℕ) : ℝ :=
  -a * Real.log n + ∑ m ∈ Finset.range n, logStep a (x + (m + 1))

theorem logRatioTailSeq_convexOn {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun x => logRatioTailSeq a x n) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy u v hu hv huv
  change 0 < x at hx
  change 0 < y at hy
  have hsum : (∑ m ∈ Finset.range n, logStep a (u * x + v * y + (m + 1))) ≤
      ∑ m ∈ Finset.range n, (u * logStep a (x + (m + 1)) +
        v * logStep a (y + (m + 1))) := by
    apply Finset.sum_le_sum
    intro m _
    have hc := (logStep_strictConvexOn ha).convexOn.2
      (show x + ((m + 1 : ℕ) : ℝ) ∈ Ioi 0 from add_pos hx (by positivity))
      (show y + ((m + 1 : ℕ) : ℝ) ∈ Ioi 0 from add_pos hy (by positivity)) hu hv huv
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one] at hc
    have he : u * (x + (m + 1)) + v * (y + (m + 1)) =
        u * x + v * y + (m + 1) := by nlinarith [huv]
    rwa [he] at hc
  simp only [logRatioTailSeq, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at *
  have he := congrArg (fun r : ℝ => r * (-a * Real.log n)) huv
  nlinarith only [hsum, he]

theorem logRatioTailSeq_eq (a x : ℝ) (n : ℕ) :
    logRatioTailSeq a x n =
      Real.BohrMollerup.logGammaSeq x n -
      Real.BohrMollerup.logGammaSeq (x + a) n - logStep a x := by
  unfold logRatioTailSeq Real.BohrMollerup.logGammaSeq
  have he : (∑ m ∈ Finset.range (n + 1), logStep a (x + m)) =
      logStep a x + ∑ m ∈ Finset.range n, logStep a (x + (m + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    ring
  have he2 : (∑ m ∈ Finset.range (n + 1), logStep a (x + m)) =
      (∑ m ∈ Finset.range (n + 1), Real.log (x + a + m)) -
      ∑ m ∈ Finset.range (n + 1), Real.log (x + m) := by
    simp only [logStep, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    ring
  rw [he] at he2
  linarith

theorem logRatioTailSeq_tendsto {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (logRatioTailSeq a x) atTop
      (𝓝 (Real.log (Real.Gamma x) - Real.log (Real.Gamma (x + a)) - logStep a x)) := by
  change Tendsto (fun n => logRatioTailSeq a x n) atTop _
  simp_rw [logRatioTailSeq_eq]
  exact ((Real.BohrMollerup.tendsto_log_gamma hx).sub
    (Real.BohrMollerup.tendsto_log_gamma (add_pos hx ha))).sub_const _

theorem logGammaRatio_sub_logStep_convexOn {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ioi 0)
      (fun x => Real.log (Real.Gamma x) - Real.log (Real.Gamma (x + a)) - logStep a x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy u v hu hv huv
  have hz : u • x + v • y ∈ Ioi (0 : ℝ) := (convex_Ioi (0 : ℝ)) hx hy hu hv huv
  exact le_of_tendsto_of_tendsto
    (logRatioTailSeq_tendsto ha hz)
    (((logRatioTailSeq_tendsto ha hx).const_mul u).add
      ((logRatioTailSeq_tendsto ha hy).const_mul v))
    (Eventually.of_forall fun n => (logRatioTailSeq_convexOn ha n).2 hx hy hu hv huv)

theorem logGammaRatio_strictConvexOn {a : ℝ} (ha : 0 < a) :
    StrictConvexOn ℝ (Ioi 0)
      (fun x => Real.log (Real.Gamma x) - Real.log (Real.Gamma (x + a))) := by
  apply ((logStep_strictConvexOn ha).add_convexOn
    (logGammaRatio_sub_logStep_convexOn ha)).congr
  intro x _
  simp only [Pi.add_apply]
  ring

#print axioms logStep_strictConvexOn
#print axioms logRatioTailSeq_tendsto
#print axioms logGammaRatio_strictConvexOn

end ConditionalSpectralExtremes
