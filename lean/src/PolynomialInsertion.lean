import ManuscriptDefinitions

/-!
Analytic polynomial estimates for the ACTUAL `circleNorm` in the revised
manuscript. No polynomial norm estimate is assumed as a hypothesis.
This module uses compactness, the maximum modulus principle, polynomial
reversal, and Cauchy's estimate from mathlib.
-/

noncomputable section
open scoped BigOperators
open Polynomial Metric Set

namespace ConditionalSpectralExtremes

theorem polynomial_unit_maximizer (p : Polynomial ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ ‖p.eval z‖ := by
  have hc : IsCompact {z : ℂ | ‖z‖ = 1} := by
    simpa only [sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) 1
  have hn : ({z : ℂ | ‖z‖ = 1} : Set ℂ).Nonempty := ⟨1, by simp⟩
  obtain ⟨z, hz, hm⟩ := hc.exists_isMaxOn hn p.continuous.norm.continuousOn
  exact ⟨z, hz, fun w hw => hm hw⟩

theorem circleNorm_bddAbove (p : Polynomial ℂ) :
    BddAbove {r : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ r = ‖p.eval z‖} := by
  obtain ⟨z, hz, hm⟩ := polynomial_unit_maximizer p
  refine ⟨‖p.eval z‖, ?_⟩
  rintro r ⟨w, hw, rfl⟩
  exact hm w hw

theorem norm_eval_le_circleNorm (p : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖p.eval z‖ ≤ circleNorm p := by
  exact le_csSup (circleNorm_bddAbove p) ⟨z, hz, rfl⟩

theorem circleNorm_le (p : Polynomial ℂ) (C : ℝ)
    (hC : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ C) : circleNorm p ≤ C := by
  apply csSup_le
  · exact ⟨‖p.eval 1‖, 1, by simp, rfl⟩
  · rintro r ⟨z, hz, rfl⟩
    exact hC z hz

theorem circleNorm_attained (p : Polynomial ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖p.eval z‖ = circleNorm p := by
  obtain ⟨z, hz, hm⟩ := polynomial_unit_maximizer p
  exact ⟨z, hz, le_antisymm (norm_eval_le_circleNorm p z hz) (circleNorm_le p _ hm)⟩

theorem circleNorm_nonneg (p : Polynomial ℂ) : 0 ≤ circleNorm p :=
  (norm_nonneg (p.eval 1)).trans (norm_eval_le_circleNorm p 1 (by simp))

/-- Maximum modulus principle on the actual closed unit disk. -/
theorem norm_eval_le_circleNorm_of_norm_le_one
    (p : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖p.eval z‖ ≤ circleNorm p := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball (0 : ℂ) 1) isBounded_ball p.differentiable.diffContOnCl
  · intro w hw
    apply norm_eval_le_circleNorm
    simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      mem_sphere, dist_zero_right] using hw
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      mem_closedBall, dist_zero_right] using hz

theorem reverse_eval_identity (p : Polynomial ℂ) (z : ℂ) (hz : z ≠ 0) :
    p.reverse.eval z⁻¹ * z ^ p.natDegree = p.eval z := by
  let _ : Invertible z := invertibleOfNonzero hz
  simpa only [invOf_eq_inv, eval₂_id] using
    Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z p

theorem reverse_boundary_bound (p : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖p.reverse.eval z‖ ≤ circleNorm p := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hid := reverse_eval_identity p z⁻¹ (inv_ne_zero hz0)
  have hh := congrArg norm hid
  simp only [inv_inv, norm_mul, norm_pow, norm_inv, hz, inv_one, one_pow, mul_one] at hh
  rw [hh]
  exact norm_eval_le_circleNorm p z⁻¹ (by simp [hz])

theorem reverse_circleNorm_le (p : Polynomial ℂ) :
    circleNorm p.reverse ≤ circleNorm p :=
  circleNorm_le p.reverse _ (reverse_boundary_bound p)

/-- Exterior polynomial growth, obtained from the reversed polynomial. -/
theorem norm_eval_le_power_circleNorm (p : Polynomial ℂ) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖p.eval z‖ ≤ ‖z‖ ^ p.natDegree * circleNorm p := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hz))
  have hinv : ‖z⁻¹‖ ≤ 1 := by simpa only [norm_inv] using inv_le_one_of_one_le₀ hz
  have hb := (norm_eval_le_circleNorm_of_norm_le_one p.reverse z⁻¹ hinv).trans
    (reverse_circleNorm_le p)
  rw [← reverse_eval_identity p z hz0, norm_mul, norm_pow]
  nlinarith [pow_nonneg (norm_nonneg z) p.natDegree]

theorem circleNorm_pos (p : Polynomial ℂ) (hp : p ≠ 0) : 0 < circleNorm p := by
  by_contra hn
  have hzero : circleNorm p = 0 := le_antisymm (by linarith) (circleNorm_nonneg p)
  apply hp
  apply Polynomial.funext
  intro z
  have hnorm : ‖p.eval z‖ ≤ 0 := by
    by_cases hz : ‖z‖ ≤ 1
    · simpa [hzero] using norm_eval_le_circleNorm_of_norm_le_one p z hz
    · simpa [hzero] using norm_eval_le_power_circleNorm p z (by linarith)
  simpa using norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

theorem norm_eval_le_radius_power (p : Polynomial ℂ) (R : ℝ) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖p.eval z‖ ≤ R ^ p.natDegree * circleNorm p := by
  by_cases hsmall : ‖z‖ ≤ 1
  · have hp := norm_eval_le_circleNorm_of_norm_le_one p z hsmall
    have hpow : 1 ≤ R ^ p.natDegree := one_le_pow₀ hR
    nlinarith [circleNorm_nonneg p]
  · exact (norm_eval_le_power_circleNorm p z (by linarith)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg z) hz p.natDegree) (circleNorm_nonneg p))

theorem one_add_inv_nat_pow_le_exp (d : ℕ) (hd : 0 < d) :
    (1 + (d : ℝ)⁻¹) ^ d ≤ Real.exp 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  calc
    (1 + (d : ℝ)⁻¹) ^ d ≤ (Real.exp ((d : ℝ)⁻¹)) ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp ((d : ℝ)⁻¹)
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_inv_cancel₀ hd0]

/-- The manuscript's first polynomial estimate, with e written exp(1). -/
theorem polynomial_derivative_bound (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖p.derivative.eval z‖ ≤ Real.exp 1 * (p.natDegree : ℝ) * circleNorm p := by
  have hdpos : 0 < (p.natDegree : ℝ) := by exact_mod_cast hd
  have hr : 0 < (p.natDegree : ℝ)⁻¹ := inv_pos.mpr hdpos
  have hboundary : ∀ w ∈ sphere z (p.natDegree : ℝ)⁻¹,
      ‖p.eval w‖ ≤ Real.exp 1 * circleNorm p := by
    intro w hw
    have hdist : ‖w - z‖ = (p.natDegree : ℝ)⁻¹ := by
      simpa only [mem_sphere, dist_eq_norm] using hw
    have hnormw : ‖w‖ ≤ 1 + (p.natDegree : ℝ)⁻¹ := by
      have hh := norm_add_le (w - z) z
      rw [sub_add_cancel] at hh
      linarith
    exact (norm_eval_le_radius_power p (1 + (p.natDegree : ℝ)⁻¹)
      (by linarith) w hnormw).trans
      (mul_le_mul_of_nonneg_right (one_add_inv_nat_pow_le_exp p.natDegree hd)
        (circleNorm_nonneg p))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr p.differentiable.diffContOnCl hboundary
  simpa only [p.deriv, div_inv_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hc

/-- A quantitative mean-value estimate on the closed unit disk. -/
theorem polynomial_unit_lipschitz (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖p.eval z - p.eval w‖ ≤
      (Real.exp 1 * (p.natDegree : ℝ) * circleNorm p) * ‖z - w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (s := closedBall (0 : ℂ) 1) (fun _ _ => p.differentiableAt)
  · intro x hx
    rw [p.deriv]
    exact polynomial_derivative_bound p hd x (by simpa using hx)
  · exact convex_closedBall (0 : ℂ) 1
  · simpa using hw
  · simpa using hz

def insertionRadius (p : Polynomial ℂ) : ℝ :=
  1 - (2 * Real.exp 1 * (p.natDegree : ℝ))⁻¹

theorem insertionRadius_bounds (p : Polynomial ℂ) (hd : 0 < p.natDegree) :
    0 ≤ insertionRadius p ∧ insertionRadius p < 1 := by
  have hd1 : 1 ≤ (p.natDegree : ℝ) := by exact_mod_cast hd
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hm : 1 ≤ Real.exp 1 * (p.natDegree : ℝ) :=
    one_le_mul_of_one_le_of_one_le he1 hd1
  have hden : 1 ≤ 2 * Real.exp 1 * (p.natDegree : ℝ) := by nlinarith
  have hi := inv_le_one_of_one_le₀ hden
  have hip : 0 < (2 * Real.exp 1 * (p.natDegree : ℝ))⁻¹ := inv_pos.mpr (by linarith)
  unfold insertionRadius
  constructor <;> linarith

theorem radial_distance (r : ℝ) (hr : r ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(r : ℂ) * z - z‖ = 1 - r := by
  calc
    ‖(r : ℂ) * z - z‖ = ‖((r - 1 : ℝ) : ℂ) * z‖ := by
      congr 1
      push_cast
      ring
    _ = |r - 1| := by simp only [norm_mul, Complex.norm_real, hz, mul_one, Real.norm_eq_abs]
    _ = 1 - r := by rw [abs_of_nonpos (by linarith)]; ring

/-- The actual radial half-maximum estimate used in insertion stability. -/
theorem polynomial_radial_half_max (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (z : ℂ) (hz : ‖z‖ = 1) (hmax : ‖p.eval z‖ = circleNorm p) :
    circleNorm p / 2 ≤ ‖p.eval ((insertionRadius p : ℂ) * z)‖ := by
  have hr := insertionRadius_bounds p hd
  have hrad : ‖(insertionRadius p : ℂ) * z‖ ≤ 1 := by
    simpa [norm_mul, hz, abs_of_nonneg hr.1] using hr.2.le
  have hl := polynomial_unit_lipschitz p hd ((insertionRadius p : ℂ) * z) z hrad hz.le
  rw [radial_distance _ hr.2.le z hz] at hl
  have hden : 2 * Real.exp 1 * (p.natDegree : ℝ) ≠ 0 := by
    have hdpos : 0 < (p.natDegree : ℝ) := by exact_mod_cast hd
    positivity
  have heq : (Real.exp 1 * (p.natDegree : ℝ) * circleNorm p) *
      (1 - insertionRadius p) = circleNorm p / 2 := by
    unfold insertionRadius
    field_simp
    ring
  rw [heq] at hl
  have ht := norm_sub_norm_le (p.eval z) (p.eval ((insertionRadius p : ℂ) * z))
  rw [hmax, norm_sub_rev] at ht
  linarith

/-- The actual polynomial product of inserted cycle factors. -/
def cycleProduct : List ℕ → Polynomial ℂ
  | [] => 1
  | j :: J => (1 - X ^ j) * cycleProduct J

theorem cycleProduct_eval_zero (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    (cycleProduct J).eval 0 = 1 := by
  induction J with
  | nil => simp [cycleProduct]
  | cons j J ih =>
      have hj : j ≠ 0 := Nat.ne_of_gt (hJ j (by simp))
      simp [cycleProduct, hj, ih (fun k hk => hJ k (by simp [hk]))]

theorem cycleProduct_ne_zero (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    cycleProduct J ≠ 0 := by
  intro h
  have hh := cycleProduct_eval_zero J hJ
  rw [h] at hh
  simp at hh

theorem cycleProduct_boundary_upper (J : List ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(cycleProduct J).eval z‖ ≤ (2 : ℝ) ^ J.length := by
  induction J with
  | nil => simp [cycleProduct]
  | cons j J ih =>
      have hf : ‖(1 : ℂ) - z ^ j‖ ≤ 2 := by
        simpa [norm_pow, hz, one_add_one_eq_two] using norm_sub_le (1 : ℂ) (z ^ j)
      simp only [cycleProduct, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
        norm_mul, List.length_cons, pow_succ]
      have hm := mul_le_mul hf ih (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith

theorem insertion_norm_upper (p : Polynomial ℂ) (J : List ℕ) :
    circleNorm (p * cycleProduct J) ≤ (2 : ℝ) ^ J.length * circleNorm p := by
  apply circleNorm_le
  intro z hz
  rw [eval_mul, norm_mul]
  have hm := mul_le_mul (norm_eval_le_circleNorm p z hz)
    (cycleProduct_boundary_upper J z hz) (norm_nonneg _) (circleNorm_nonneg p)
  simpa only [mul_comm] using hm

/-- The upper half of the manuscript's insertion stability lemma. -/
theorem insertion_log_upper (p : Polynomial ℂ) (hp : p ≠ 0)
    (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    Real.log (circleNorm (p * cycleProduct J)) - Real.log (circleNorm p) ≤
      (J.length : ℝ) * Real.log 2 := by
  have hP := circleNorm_pos p hp
  have hPQ := circleNorm_pos (p * cycleProduct J) (mul_ne_zero hp (cycleProduct_ne_zero J hJ))
  have hl := Real.log_le_log hPQ (insertion_norm_upper p J)
  rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at hl
  linarith

/-- The scalar logarithmic estimate actually used in the insertion proof. -/
theorem neg_inv_le_log_one_sub_exp_neg (x : ℝ) (hx : 0 < x) :
    -x⁻¹ ≤ Real.log (1 - Real.exp (-x)) := by
  have he : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hm : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgap : 0 < 1 - Real.exp (-x) := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hgap
  have hlin : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hi : (Real.exp x - 1)⁻¹ ≤ x⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hx hlin
  have heq : 1 - (1 - Real.exp (-x))⁻¹ = -(Real.exp x - 1)⁻¹ := by
    rw [Real.exp_neg]
    have he0 : Real.exp x ≠ 0 := Real.exp_ne_zero x
    have hed : Real.exp x - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [heq] at hlog
  linarith

theorem radial_factor_log_lower (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ = 1) (j : ℕ) (hj : 0 < j) :
    0 < ‖(1 : ℂ) - ((r : ℂ) * z) ^ j‖ ∧
    -(1 - r)⁻¹ * (j : ℝ)⁻¹ ≤ Real.log ‖(1 : ℂ) - ((r : ℂ) * z) ^ j‖ := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hpow : r ^ j < 1 := pow_lt_one₀ hr0 hr1 (Nat.ne_of_gt hj)
  have hgap : 0 < 1 - r ^ j := by linarith
  have hn : 1 - r ^ j ≤ ‖(1 : ℂ) - ((r : ℂ) * z) ^ j‖ := by
    simpa [norm_pow, norm_mul, hz, abs_of_nonneg hr0] using
      norm_sub_norm_le (1 : ℂ) (((r : ℂ) * z) ^ j)
  have hnpos : 0 < ‖(1 : ℂ) - ((r : ℂ) * z) ^ j‖ := lt_of_lt_of_le hgap hn
  have hexp : r ≤ Real.exp (-(1 - r)) := by
    have hh := Real.add_one_le_exp (-(1 - r))
    linarith
  have hp : r ^ j ≤ Real.exp (-((j : ℝ) * (1 - r))) := by
    have hh := pow_le_pow_left₀ hr0 hexp j
    rw [← Real.exp_nat_mul] at hh
    simpa only [mul_neg] using hh
  have hx : 0 < (j : ℝ) * (1 - r) := mul_pos hjR (by linarith)
  have hg : 0 < 1 - Real.exp (-((j : ℝ) * (1 - r))) := by
    have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
    linarith
  have hlog := (neg_inv_le_log_one_sub_exp_neg _ hx).trans
    ((Real.log_le_log hg (sub_le_sub_left hp 1)).trans (Real.log_le_log hgap hn))
  refine ⟨hnpos, ?_⟩
  simpa only [mul_inv_rev, neg_mul] using hlog

theorem cycleProduct_radial_log_lower (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (z : ℂ) (hz : ‖z‖ = 1) :
    0 < ‖(cycleProduct J).eval ((r : ℂ) * z)‖ ∧
    -(1 - r)⁻¹ * (J.map (fun j : ℕ => (j : ℝ)⁻¹)).sum ≤
      Real.log ‖(cycleProduct J).eval ((r : ℂ) * z)‖ := by
  induction J with
  | nil => simp [cycleProduct]
  | cons j J ih =>
      have hj := hJ j (by simp)
      have ht := ih (fun k hk => hJ k (by simp [hk]))
      have hf := radial_factor_log_lower r hr0 hr1 z hz j hj
      simp only [cycleProduct, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
        norm_mul, List.map_cons, List.sum_cons]
      constructor
      · exact mul_pos hf.1 ht.1
      · rw [Real.log_mul hf.1.ne' ht.1.ne']
        linarith [hf.2, ht.2]

/-- The lower half of the actual insertion lemma, including its 2ed constant. -/
theorem insertion_log_lower (p : Polynomial ℂ) (hp : p ≠ 0)
    (hd : 0 < p.natDegree) (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    -Real.log 2 - 2 * Real.exp 1 * (p.natDegree : ℝ) *
        (J.map (fun j : ℕ => (j : ℝ)⁻¹)).sum ≤
      Real.log (circleNorm (p * cycleProduct J)) - Real.log (circleNorm p) := by
  obtain ⟨z, hz, hmax⟩ := circleNorm_attained p
  have hr := insertionRadius_bounds p hd
  have hrad : ‖(insertionRadius p : ℂ) * z‖ ≤ 1 := by
    simpa [norm_mul, hz, abs_of_nonneg hr.1] using hr.2.le
  have hP := circleNorm_pos p hp
  have hhalf := polynomial_radial_half_max p hd z hz hmax
  have hPr : 0 < ‖p.eval ((insertionRadius p : ℂ) * z)‖ :=
    lt_of_lt_of_le (by positivity) hhalf
  have hQ := cycleProduct_radial_log_lower J hJ (insertionRadius p) hr.1 hr.2 z hz
  have hinside := norm_eval_le_circleNorm_of_norm_le_one
    (p * cycleProduct J) ((insertionRadius p : ℂ) * z) hrad
  rw [eval_mul, norm_mul] at hinside
  have hlog := Real.log_le_log (mul_pos hPr hQ.1) hinside
  rw [Real.log_mul hPr.ne' hQ.1.ne'] at hlog
  have hPlog := Real.log_le_log (show 0 < circleNorm p / 2 by positivity) hhalf
  rw [Real.log_div hP.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hPlog
  have hQlog := hQ.2
  have hdelta : (1 - insertionRadius p)⁻¹ =
      2 * Real.exp 1 * (p.natDegree : ℝ) := by
    simp only [insertionRadius, sub_sub_cancel, inv_inv]
  rw [hdelta] at hQlog
  linarith

theorem polynomial_insertion_stability (p : Polynomial ℂ) (hp : p ≠ 0)
    (hd : 0 < p.natDegree) (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    -Real.log 2 - 2 * Real.exp 1 * (p.natDegree : ℝ) *
        (J.map (fun j : ℕ => (j : ℝ)⁻¹)).sum ≤
      Real.log (circleNorm (p * cycleProduct J)) - Real.log (circleNorm p) ∧
    Real.log (circleNorm (p * cycleProduct J)) - Real.log (circleNorm p) ≤
      (J.length : ℝ) * Real.log 2 :=
  ⟨insertion_log_lower p hp hd J hJ, insertion_log_upper p hp J hJ⟩

theorem circleNorm_C (a : ℂ) : circleNorm (C a) = ‖a‖ := by
  apply le_antisymm
  · apply circleNorm_le
    intro z _
    simp
  · simpa using norm_eval_le_circleNorm (C a) 1 (by simp)

/-- The separate d=0 lower bound in the manuscript is exactly zero. -/
theorem insertion_log_lower_degree_zero (p : Polynomial ℂ) (hp : p ≠ 0)
    (hd : p.natDegree = 0) (J : List ℕ) (hJ : ∀ j ∈ J, 0 < j) :
    0 ≤ Real.log (circleNorm (p * cycleProduct J)) - Real.log (circleNorm p) := by
  have heq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hN : circleNorm p = ‖p.eval 0‖ := by rw [heq, circleNorm_C, eval_C]
  have hb := norm_eval_le_circleNorm_of_norm_le_one (p * cycleProduct J) 0 (by simp)
  rw [eval_mul, cycleProduct_eval_zero J hJ, mul_one, ← hN] at hb
  have hl := Real.log_le_log (circleNorm_pos p hp) hb
  linarith

theorem cycle_factor_natDegree (j : ℕ) (hj : 0 < j) :
    (1 - (X : Polynomial ℂ) ^ j).natDegree = j := by
  have hh : (1 : Polynomial ℂ).natDegree < ((X : Polynomial ℂ) ^ j).natDegree := by
    simpa using hj
  simpa using natDegree_sub_eq_right_of_natDegree_lt hh

/-- The actual finite permutation polynomial has its exact size degree. -/
theorem characteristicPolynomial_natDegree {n : ℕ} (c : Configuration n) :
    (characteristicPolynomial c).natDegree = totalSize c := by
  classical
  have hf : ∀ j : Fin n, (1 - (X : Polynomial ℂ) ^ (j.val + 1)) ≠ 0 := by
    intro j h
    have hh := congrArg (fun p : Polynomial ℂ => p.eval 0) h
    simp at hh
  unfold characteristicPolynomial totalSize
  rw [natDegree_prod Finset.univ _ (fun j _ => pow_ne_zero _ (hf j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [natDegree_pow, cycle_factor_natDegree _ (Nat.succ_pos _)]
  exact Nat.mul_comm _ _

theorem characteristicPolynomial_natDegree_of_valid {n k : ℕ}
    (c : Configuration n) (hc : Valid k c) :
    (characteristicPolynomial c).natDegree = n :=
  (characteristicPolynomial_natDegree c).trans hc.1

theorem characteristicPolynomial_circleNorm_ge_one {n : ℕ} (c : Configuration n) :
    1 ≤ circleNorm (characteristicPolynomial c) := by
  have hh := norm_eval_le_circleNorm_of_norm_le_one (characteristicPolynomial c) 0 (by simp)
  simpa only [characteristicPolynomial_eval_zero, norm_one] using hh

theorem maximumLogModulus_nonneg {n : ℕ} (c : Configuration n) :
    0 ≤ maximumLogModulus c :=
  Real.log_nonneg (characteristicPolynomial_circleNorm_ge_one c)

#print axioms polynomial_unit_maximizer
#print axioms circleNorm_bddAbove
#print axioms norm_eval_le_circleNorm
#print axioms circleNorm_le
#print axioms circleNorm_attained
#print axioms circleNorm_nonneg
#print axioms norm_eval_le_circleNorm_of_norm_le_one
#print axioms reverse_eval_identity
#print axioms reverse_boundary_bound
#print axioms reverse_circleNorm_le
#print axioms norm_eval_le_power_circleNorm
#print axioms circleNorm_pos
#print axioms norm_eval_le_radius_power
#print axioms one_add_inv_nat_pow_le_exp
#print axioms polynomial_derivative_bound
#print axioms polynomial_unit_lipschitz
#print axioms insertionRadius_bounds
#print axioms radial_distance
#print axioms polynomial_radial_half_max
#print axioms cycleProduct_eval_zero
#print axioms cycleProduct_ne_zero
#print axioms cycleProduct_boundary_upper
#print axioms insertion_norm_upper
#print axioms insertion_log_upper
#print axioms neg_inv_le_log_one_sub_exp_neg
#print axioms radial_factor_log_lower
#print axioms cycleProduct_radial_log_lower
#print axioms insertion_log_lower
#print axioms polynomial_insertion_stability
#print axioms circleNorm_C
#print axioms insertion_log_lower_degree_zero
#print axioms cycle_factor_natDegree
#print axioms characteristicPolynomial_natDegree
#print axioms characteristicPolynomial_natDegree_of_valid
#print axioms characteristicPolynomial_circleNorm_ge_one
#print axioms maximumLogModulus_nonneg

end ConditionalSpectralExtremes
