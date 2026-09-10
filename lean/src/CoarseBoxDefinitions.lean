import FineScaleGeometry
import CenterMinimizer
import DyadicBoxEnergy

/-! The actual frontier, gaps, centers and group sample counts used in
Lemma boxes. The drift identity uses the proved equation of the actual
criticalPoint; it has no separate critical-equation hypothesis. -/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

def groupSamples (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j : ℕ) : ℕ :=
  countPrefix q (groupStart p n (j+1))-countPrefix q (groupStart p n j)

def fineFrontier (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) (i : ℕ) : ℝ :=
  ConditionalSpectralAudit.BoxAlgebra.frontier (coordinate p n i) (lambda (criticalPoint κ))
    (countPrefix q i) (criticalPoint κ)

def terminalHeight (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) : ℝ :=
  (aStar n-r p n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ

def gap (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j=0 then r p n/criticalPoint κ
  else if j=groupNumber p n then r p n/criticalPoint κ-1/2
  else 4*G+B₀*(Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)+
    Real.sqrt (groupWidth p n j)*environmentE p n κ q j)

def boxCenter (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  fineFrontier p n κ q (groupStart p n j)-gap p n κ G B₀ q j

def groupU (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  dyadicBoxU (groupNumber p n) (fun i => groupWidth p n (i-1)) (paddedE p n κ q) (r p n) j

theorem groupSamples_end (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j : ℕ)
    (hj : j < groupNumber p n) :
    countPrefix q (groupStart p n (j+1)) =
      countPrefix q (groupStart p n j)+groupSamples p n q j := by
  have hstart : groupStart p n j ≤ groupStart p n (j+1) := by
    rw [group_start_step p n j hj]
    omega
  have hprefix := countPrefix_mono q hstart
  unfold groupSamples
  omega

theorem groupSamples_cast (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j : ℕ)
    (hj : j < groupNumber p n) :
    (groupSamples p n q j : ℝ) =
      (countPrefix q (groupStart p n (j+1)) : ℝ)-countPrefix q (groupStart p n j) := by
  have hh := congrArg (fun a : ℕ => (a : ℝ)) (groupSamples_end p n q j hj)
  push_cast at hh
  linarith

theorem boxCenter_zero (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) :
    boxCenter p n κ G B₀ q 0 = 0 := by
  simp [boxCenter, fineFrontier, gap, group_start_zero, coordinate_zero, countPrefix_zero,
    ConditionalSpectralAudit.BoxAlgebra.frontier]

theorem boxCenter_last (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) :
    boxCenter p n κ G B₀ q (groupNumber p n) = terminalHeight p n κ q+1/2 := by
  have hne := ConditionalSpectralAudit.DyadicGrouping.dyadic_groups_nonempty _ _ hv hm
  have hB : groupNumber p n ≠ 0 := by
    exact (List.length_pos_iff.mpr hne).ne'
  have hc : 0 < count p n := by omega
  have hs : criticalPoint κ ≠ 0 := (criticalPoint_pos hκ).ne'
  simp only [boxCenter, fineFrontier, gap, if_neg hB, ite_true,
    groupStart_last p n hv hm, coordinate_last p n hc,
    ConditionalSpectralAudit.BoxAlgebra.frontier, terminalHeight]
  field_simp
  ring

theorem actual_box_drift (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (j : ℕ) (hj : j < groupNumber p n) (e e' : ℝ) :
    (boxCenter p n κ G B₀ q (j+1)+e')-(boxCenter p n κ G B₀ q j+e)-
        (groupSamples p n q j : ℝ)*deriv lambda (criticalPoint κ) =
      (groupWidth p n j-(groupSamples p n q j : ℝ)/κ)/criticalPoint κ-
        (gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j)+(e'-e) := by
  have hs : criticalPoint κ ≠ 0 := (criticalPoint_pos hκ).ne'
  have hcritical : criticalPoint κ*deriv lambda (criticalPoint κ)-lambda (criticalPoint κ) = 1/κ := by
    apply (eq_div_iff hκ.ne').2
    nlinarith [criticalPoint_equation hκ]
  have ha : coordinate p n (groupStart p n (j+1)) =
      coordinate p n (groupStart p n j)+groupWidth p n j := by
    have hh := group_spatial_width p n j hj
    linarith
  have hS : (countPrefix q (groupStart p n (j+1)) : ℝ) =
      (countPrefix q (groupStart p n j) : ℝ)+(groupSamples p n q j : ℝ) := by
    exact_mod_cast groupSamples_end p n q j hj
  unfold boxCenter fineFrontier
  rw [ha, hS]
  exact ConditionalSpectralAudit.BoxAlgebra.box_drift
    (coordinate p n (groupStart p n j)) (countPrefix q (groupStart p n j))
    (groupWidth p n j) (groupSamples p n q j) (lambda (criticalPoint κ)) (criticalPoint κ)
    (deriv lambda (criticalPoint κ)) κ (gap p n κ G B₀ q j) (gap p n κ G B₀ q (j+1))
    e e' hs hκ.ne' hcritical

#print axioms groupSamples_end
#print axioms groupSamples_cast
#print axioms boxCenter_zero
#print axioms boxCenter_last
#print axioms actual_box_drift

end ConditionalSpectralExtremes.CoarseBoxes
