import ActualReservoirRelative
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Quantitative comparison of the actual reservoir saddle main terms. -/
noncomputable section
open Set
namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem logGamma_lipschitz_on_positive_interval {a B : ℝ} (ha : 0 < a) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ Icc a B, ∀ y ∈ Icc a B,
      |Real.log (Real.Gamma x) - Real.log (Real.Gamma y)| ≤ G * |x-y| := by
  have hl := Real.convexOn_log_Gamma.locallyLipschitzOn isOpen_Ioi
  have hs : Icc a B ⊆ Ioi 0 := fun x hx => ha.trans_le hx.1
  obtain ⟨G, hG⟩ := (hl.mono hs).exists_lipschitzOnWith_of_compact isCompact_Icc
  exact ⟨G, G.coe_nonneg, fun x hx y hy => by
    simpa only [Real.dist_eq, Function.comp_apply] using hG.dist_le_mul x hx y hy⟩

theorem log_interval_difference_bound {x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) :
    |Real.log x - Real.log t| ≤ (t-x)/x := by
  have ht := hx.trans_le hxt
  have hl := Real.log_le_sub_one_of_pos (div_pos ht hx)
  rw [Real.log_div ht.ne' hx.ne'] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx hxt))]
  have he : t / x - 1 = (t-x)/x := by field_simp
  linarith

theorem reciprocal_marker_difference {l x t B : ℝ} (hl : 0 ≤ l) (hx : 0 < x)
    (ht : 1 ≤ t) (hxt : x ≤ t) (hhalf : t/2 ≤ x) (hlB : l/t ≤ B) :
    |l/x-l/t| ≤ 2*B*(t-x) := by
  have htp : 0 < t := by linarith
  have hB : 0 ≤ B := (div_nonneg hl htp.le).trans hlB
  have hlt := (div_le_iff₀ htp).mp hlB
  have hlx : l/x ≤ 2*B := (div_le_iff₀ hx).2 (by nlinarith)
  have he : l/x-l/t = (l/x)*(t-x)/t := by field_simp
  rw [he, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*B)*(t-x)/t := by gcongr
    _ ≤ _ := div_le_self (by positivity) ht

theorem reservoirLeading_log (b N l : ℕ) (hN : 0 < N)
    (hT : 0 < reservoirTime b N) (hl : 0 < l) :
    Real.log (reservoirLeading b N l) =
      (l : ℝ)*Real.log (reservoirTime b N) - Real.log N - Real.log (l.factorial : ℝ) -
        Real.log (Real.Gamma ((l : ℝ)/reservoirTime b N)) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlp : 0 < (l : ℝ) := by exact_mod_cast hl
  have hf : 0 < (l.factorial : ℝ) := by exact_mod_cast l.factorial_pos
  have hg := Real.Gamma_pos_of_pos (div_pos hlp hT)
  unfold reservoirLeading
  rw [Real.log_div (pow_pos hT _).ne' (by positivity), Real.log_pow,
    Real.log_mul (by positivity : (N : ℝ) * l.factorial ≠ 0) hg.ne',
    Real.log_mul hNp.ne' hf.ne']
  ring

theorem reservoirLeading_log_ratio_bound {a B : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ b N n l : ℕ, 0 < N → 0 < n → 0 < l →
      1 ≤ reservoirTime b n →
      reservoirTime b n / 2 ≤ reservoirTime b N →
      reservoirTime b N ≤ reservoirTime b n →
      a ≤ (l : ℝ)/reservoirTime b n → (l : ℝ)/reservoirTime b n ≤ B →
      |Real.log (reservoirLeading b N l / reservoirLeading b n l)| ≤
        K * |reservoirTime b N - reservoirTime b n| := by
  obtain ⟨G, hG, hg⟩ := logGamma_lipschitz_on_positive_interval (B := 2*max a B) ha
  refine ⟨2*max a B + 1 + G*(2*max a B), by positivity, ?_⟩
  intro b N n l hN hn hl ht hx hxt hal hlB
  let t := reservoirTime b n
  let x := reservoirTime b N
  have htp : 0 < t := by dsimp [t]; linarith
  have hxp : 0 < x := by dsimp [x]; linarith
  have hlp : 0 < (l : ℝ) := by exact_mod_cast hl
  have hB : 0 < B := ha.trans_le (hal.trans hlB)
  have hlt := (div_le_iff₀ htp).mp hlB
  have hll : a ≤ (l : ℝ)/x := by
    exact hal.trans (div_le_div_of_nonneg_left hlp.le hxp hxt)
  have hlu : (l : ℝ)/x ≤ 2*max a B := by
    apply (div_le_iff₀ hxp).2
    have hBm : B ≤ max a B := le_max_right _ _
    have hm : 0 ≤ max a B := (ha.trans_le (le_max_left _ _)).le
    dsimp [x, t] at *
    nlinarith
  have hΓ := hg ((l : ℝ)/x) ⟨hll, hlu⟩ ((l : ℝ)/t)
    ⟨hal, hlB.trans (by have := le_max_right a B; have := le_max_left a B; linarith)⟩
  have hdr := reciprocal_marker_difference hlp.le hxp ht hxt hx
    (hlB.trans (le_max_right a B))
  have hlog := log_interval_difference_bound hxp hxt
  have hmul : |(l : ℝ) * (Real.log x - Real.log t)| ≤ (2*max a B)*(t-x) := by
    rw [abs_mul, abs_of_pos hlp]
    calc
      _ ≤ (l : ℝ)*((t-x)/x) := mul_le_mul_of_nonneg_left hlog hlp.le
      _ = ((l : ℝ)/x)*(t-x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlu (sub_nonneg.mpr hxt)
  have hΓ' : |Real.log (Real.Gamma ((l : ℝ)/x))-Real.log (Real.Gamma ((l : ℝ)/t))| ≤
      G*(2*max a B)*(t-x) := by nlinarith [mul_le_mul_of_nonneg_left hdr hG]
  have he : Real.log (reservoirLeading b N l / reservoirLeading b n l) =
      (l : ℝ)*(Real.log x-Real.log t) - (x-t) -
        (Real.log (Real.Gamma ((l : ℝ)/x))-Real.log (Real.Gamma ((l : ℝ)/t))) := by
    rw [Real.log_div (reservoirLeading_pos hN hxp hl).ne'
      (reservoirLeading_pos hn htp hl).ne', reservoirLeading_log b N l hN hxp hl,
      reservoirLeading_log b n l hn htp hl]
    dsimp [x, t, reservoirTime]
    ring
  rw [he]
  have habs : |x-t| = t-x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxt)]
    ring
  have hab (u v : ℝ) : |u-v| ≤ |u|+|v| := by simpa using abs_sub_le u 0 v
  have htri := (hab ((l : ℝ)*(Real.log x-Real.log t)-(x-t))
    (Real.log (Real.Gamma ((l : ℝ)/x))-Real.log (Real.Gamma ((l : ℝ)/t)))).trans
    (add_le_add (hab ((l : ℝ)*(Real.log x-Real.log t)) (x-t)) le_rfl)
  change _ ≤ _ * |x-t|
  rw [habs] at *
  nlinarith

#print axioms reservoirLeading_log_ratio_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
