import CoarseBoxDefinitions
import FineGroupWidthGeometry

/-! Quantitative boundary controls: the regular E sqrt(H) cost is
K_E r sqrt(2/D), so choosing D is independent of fixed gStar,rStar. -/

noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem boundary_gap_variation_bound (r s smin G B₀ V ε T : ℝ)
    (hr : 0 ≤ r) (hsmin : 0 < smin) (hs : smin ≤ s)
    (hG : 0 ≤ G) (hGr : G ≤ r/smin) (hB : 0 ≤ B₀)
    (hV : 0 ≤ V) (hVT : V ≤ 3*T) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hT : 1 ≤ T) (hrT : r ≤ T) :
    |4*G+B₀*V-(r/s-ε)| ≤ (5/smin+3*B₀+1)*T := by
  have hsp : 0 < s := hsmin.trans_le hs
  have hratio := div_le_div_of_nonneg_left hr hsmin hs
  have hrbound := div_le_div_of_nonneg_right hrT hsmin.le
  have habs := abs_sub (4*G+B₀*V) (r/s-ε)
  rw [abs_of_nonneg (by positivity : 0 ≤ 4*G+B₀*V)] at habs
  have hsecond : |r/s-ε| ≤ r/s+ε := by
    simpa only [abs_of_nonneg (div_nonneg hr hsp.le), abs_of_nonneg hε] using abs_sub (r/s) ε
  have hprod := mul_le_mul_of_nonneg_left hVT hB
  have hid : (5/smin+3*B₀+1)*T = 5*(T/smin)+3*B₀*T+T := by ring
  rw [hid]
  linarith

theorem boundary_endpoint_margin (r s smax G Z ε e : ℝ)
    (hs : 0 < s) (hsmax : s ≤ smax) (hr : 2*smax ≤ r)
    (hG : G ≤ r/(64*smax)) (hZ : Z ≤ r/(8*smax))
    (he : ε+e ≤ 1) :
    2*G+Z ≤ (r/s-ε)-e := by
  have hmax : 0 < smax := hs.trans_le hsmax
  have hrpos : 0 ≤ r := (by positivity : (0 : ℝ) ≤ 2*smax).trans hr
  have hratio := div_le_div_of_nonneg_left hrpos hs hsmax
  have hGr : 64*smax*G ≤ r := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<64*smax)).1 hG
    nlinarith
  have hZr : 8*smax*Z ≤ r := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<8*smax)).1 hZ
    nlinarith
  have hmargin : 2*G+Z+1 ≤ r/smax := by
    apply (le_div_iff₀ hmax).2
    nlinarith
  linarith

theorem regular_boundary_energy (p : Parameters) (n : ℕ) (κ η K_E C_E : ℝ)
    (q : ℕ → ℕ) (hreg : Regular p n κ η K_E C_E q)
    (hKE : 0 ≤ K_E) (hr : 0 ≤ r p n) (hD : 0 < p.D₀)
    (hlog : 0 < Real.log (ReservoirScale.ell n))
    (j : ℕ) (hj : j < groupNumber p n)
    (hH : groupWidth p n j ≤ 2*baseWidth p n) :
    environmentE p n κ q j*Real.sqrt (groupWidth p n j) ≤
      K_E*r p n*Real.sqrt (2/p.D₀) := by
  have hE := hreg.2.1 j (Finset.mem_range.mpr hj)
  have hmul := mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg (groupWidth p n j))
  have hwidth : Real.sqrt (Real.log (ReservoirScale.ell n))*Real.sqrt (groupWidth p n j) ≤
      r p n*Real.sqrt (2/p.D₀) := by
    rw [← Real.sqrt_mul hlog.le]
    have hb := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hH hlog.le)
    have hid : Real.log (ReservoirScale.ell n)*(2*baseWidth p n) = (2/p.D₀)*(r p n)^2 := by
      unfold baseWidth
      field_simp
    rw [hid, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2/p.D₀), Real.sqrt_sq hr] at hb
    simpa only [mul_comm] using hb
  have hb := mul_le_mul_of_nonneg_left hwidth hKE
  nlinarith

#print axioms boundary_gap_variation_bound
#print axioms boundary_endpoint_margin
#print axioms regular_boundary_energy

end ConditionalSpectralExtremes.CoarseBoxes
