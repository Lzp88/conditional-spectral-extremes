import BoxChordMargin

/-! Both margins for every actual endpoint box. The only size conditions
on B_0,D_0 are explicit scalar inequalities independent of gStar,rStar. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem actual_box_endpoint_margins (p : Parameters) (n : ℕ)
    (κ η K_E C_E G B₀ W A α smin smax : ℝ) (q : ℕ → ℕ)
    (hreg : Regular p n κ η K_E C_E q) (hKE : 0 ≤ K_E)
    (hG : 0 ≤ G) (hW : 0 ≤ W) (hA : 0 ≤ A) (hα : 0 < α)
    (hsmin : 0 < smin) (hslo : smin ≤ criticalPoint κ) (hshi : criticalPoint κ ≤ smax)
    (hB₀ : 2+(W*Real.sqrt A+2/(α*smin)) ≤ B₀)
    (hD : 0 < p.D₀) (hDsmall : (W*Real.sqrt A+2/(α*smin))*K_E*Real.sqrt (2/p.D₀) ≤ 1/(8*smax))
    (hr : 2*smax ≤ r p n) (hGr : G ≤ r p n/(64*smax))
    (hω : 0 < omega p n) (hb : 0 < baseWidth p n) (hωb : omega p n ≤ baseWidth p n)
    (hm : 6*baseBlocks p n ≤ count p n) (hlog : 0 < Real.log (ReservoirScale.ell n))
    (j : ℕ) (hj : j < groupNumber p n)
    (hQ : (groupSamples p n q j : ℝ) ≤ A*groupWidth p n j)
    (e e' : ℝ) (he : |e| ≤ 2*Real.sqrt (groupWidth p n j))
    (he' : |e'| ≤ 2*Real.sqrt (groupWidth p n j))
    (hezero : j=0 → e=0) (helast : j+1=groupNumber p n → |e'| ≤ 1/10) :
    (2*G+W*Real.sqrt (groupSamples p n q j : ℝ)+
        (2/α)*environmentE p n κ q j*Real.sqrt (groupWidth p n j)/criticalPoint κ ≤
      gap p n κ G B₀ q j-e) ∧
    (2*G+W*Real.sqrt (groupSamples p n q j : ℝ)+
        (2/α)*environmentE p n κ q j*Real.sqrt (groupWidth p n j)/criticalPoint κ ≤
      gap p n κ G B₀ q (j+1)-e') := by
  let C := W*Real.sqrt A+2/(α*smin)
  let Z := W*Real.sqrt (groupSamples p n q j : ℝ)+
    (2/α)*environmentE p n κ q j*Real.sqrt (groupWidth p n j)/criticalPoint κ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBpos : 0 ≤ B₀ := by change 2+C ≤ B₀ at hB₀; linarith
  have hsp : 0 < criticalPoint κ := hsmin.trans_le hslo
  have hsmax : 0 < smax := hsp.trans_le hshi
  have hrpos : 0 ≤ r p n := le_trans (by positivity : (0 : ℝ) ≤ 2*smax) hr
  have hH := groupWidth_ge_base p n j hω hb (by omega) hj
  have hHpos := hb.trans_le hH
  have hE : 1 ≤ environmentE p n κ q j := localE_ge_one _ _ _ _ _
  have hZ : Z ≤ C*(Real.sqrt (groupWidth p n j)*environmentE p n κ q j) :=
    bridge_margin_scale_bound _ _ α A (criticalPoint κ) smin _ W hHpos.le hα hA hsmin hslo hE hW hQ
  have hboundary := groupWidth_boundary_le_two_base p n hω hb hωb hm
  have hcost (hwidth : groupWidth p n j ≤ 2*baseWidth p n) : Z ≤ r p n/(8*smax) :=
    hZ.trans (regular_boundary_margin_cost p n κ η K_E C_E C smax q hreg hKE hC hrpos hD
      hlog hDsmall j hj hwidth)
  constructor
  · by_cases hj0 : j=0
    · have he0 := hezero hj0
      have hwidth : groupWidth p n j ≤ 2*baseWidth p n := by simpa only [hj0] using hboundary.1
      have hh := boundary_endpoint_margin (r p n) (criticalPoint κ) smax G Z 0 e
        hsp hshi hr hGr (hcost hwidth) (by simp [he0])
      have hgap : gap p n κ G B₀ q j=r p n/criticalPoint κ := by simp [gap, hj0]
      rw [hgap]
      dsimp [Z] at hh
      linarith
    · have hh := gap_margin_of_lower (gap p n κ G B₀ q j) e G B₀ C
        (environmentE p n κ q j) (groupWidth p n j) Z hG hHpos.le hE hC hB₀
        (gap_left_dominates_current p n κ G B₀ q hBpos j (by omega) hj) he hZ
      dsimp [Z] at hh
      linarith
  · by_cases hjlast : j+1=groupNumber p n
    · have hwidth : groupWidth p n j ≤ 2*baseWidth p n := by
        simpa only [show groupNumber p n-1=j by omega] using hboundary.2
      have he1 := (abs_le.mp (helast hjlast)).2
      have hh := boundary_endpoint_margin (r p n) (criticalPoint κ) smax G Z (1/2) e'
        hsp hshi hr hGr (hcost hwidth) (by linarith)
      have hgap : gap p n κ G B₀ q (j+1)=r p n/criticalPoint κ-1/2 := by
        unfold gap
        rw [if_neg (by omega), if_pos hjlast]
      rw [hgap]
      dsimp [Z] at hh
      linarith
    · have hh := gap_margin_of_lower (gap p n κ G B₀ q (j+1)) e' G B₀ C
        (environmentE p n κ q j) (groupWidth p n j) Z hG hHpos.le hE hC hB₀
        (gap_right_dominates_current p n κ G B₀ q hBpos j (by omega)) he' hZ
      dsimp [Z] at hh
      linarith

#print axioms actual_box_endpoint_margins

end ConditionalSpectralExtremes.CoarseBoxes
