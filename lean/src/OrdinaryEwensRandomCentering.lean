import OrdinaryCountLocalization
import OrdinaryCenterAlgebra
import EwensCycleGrowingProbability
import SpeedTaylorBound

/-! The ordinary-Ewens fixed-constant log-log random centering, on the actual
finite configuration law. The main conditional theorem is supplied explicitly
here and is discharged in the final paper wrapper. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

def ordinarySlope (θ : Real) : Real := lambda (criticalPoint θ)/criticalPoint θ

def ordinaryLinearCenter (θ : Real) (n k : Nat) : Real :=
  speed θ*Real.log n+ordinarySlope θ*((k : Real)-θ*Real.log n)

theorem ordinary_ewens_random_centering (hmain : ExactCycleLocalization) (θ : Real) (hθ : 0 < θ) :
    ∃ C : Real, 0 ≤ C ∧ Tendsto (fun n : Nat => ewensProbability θ n
      (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|))
      atTop (𝓝 0) := by
  obtain ⟨C₀,hC₀,hcenter⟩ := ordinary_random_count_localization hmain θ hθ
  obtain ⟨δ,C,hδ,hC,hδθ,hTaylor⟩ := speed_local_quadratic_remainder θ hθ
  let b : Nat → Real := fun n => Real.sqrt (Real.log (Real.log n)/(C*θ))
  have hCθ : 0 < C*θ := mul_pos hC hθ
  have hL : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hell : Tendsto (fun n : Nat => Real.log (Real.log (n : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hb : Tendsto b atTop atTop := Real.tendsto_sqrt_atTop.comp (hell.atTop_div_const hCθ)
  have htail := ewens_clt_growing_probability θ hθ b hb
  have hcount := ewens_cycle_weak_law θ hθ δ hδ
  refine ⟨C₀+1,by linarith,?_⟩
  have hupper : ∀ᶠ n : Nat in atTop,
      ewensProbability θ n (fun c => (C₀+1)*Real.log (Real.log n) <
        |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|) ≤
      ewensProbability θ n (fun c => C₀*Real.log (Real.log n)<
        |maximumLogModulus c-center n (cycleCount c)|)+
      ewensProbability θ n (fun c => δ≤|(cycleCount c : Real)/Real.log n-θ|)+
      ewensProbability θ n (fun c => b n≤|((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)|) := by
    filter_upwards [eventually_ge_atTop (2 : Nat),hL.eventually_gt_atTop 0,hell.eventually_gt_atTop 0]
      with n hn hLn helln
    apply (ewensProbability_mono θ hθ n _
      (fun c => C₀*Real.log (Real.log n) < |maximumLogModulus c-center n (cycleCount c)| ∨
        δ≤|(cycleCount c : Real)/Real.log n-θ| ∨
        b n≤|((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)|) ?_).trans
      (ewensProbability_union_three_le θ hθ n _ _ _)
    intro c _ hbad
    by_cases h1 : C₀*Real.log (Real.log n) < |maximumLogModulus c-center n (cycleCount c)|
    · exact Or.inl h1
    by_cases h2 : δ≤|(cycleCount c : Real)/Real.log n-θ|
    · exact Or.inr (Or.inl h2)
    by_cases h3 : b n≤|((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)|
    · exact Or.inr (Or.inr h3)
    have hkδ : |(cycleCount c : Real)/Real.log n-θ|≤δ := (lt_of_not_ge h2).le
    have hkpos : 0 < (cycleCount c : Real)/Real.log n := by
      linarith [(abs_le.mp hkδ).1]
    have hk : 0 < cycleCount c := by
      have hh : 0 < (cycleCount c : Real) := by simpa using (lt_div_iff₀ hLn).mp hkpos
      exact_mod_cast hh
    have ht := actual_center_quadratic_bound n (cycleCount c) θ (ordinarySlope θ) C
      (by omega) hk hθ (hTaylor _ hkδ)
    have hsq := (sq_lt_sq₀ (abs_nonneg (((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)))
      (Real.sqrt_nonneg (Real.log (Real.log n)/(C*θ)))).mpr (lt_of_not_ge h3)
    rw [sq_abs,Real.sq_sqrt (div_pos helln hCθ).le] at hsq
    have hr : C*θ*(((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n))^2 <
        Real.log (Real.log n) := by
      have hh := (lt_div_iff₀ hCθ).mp hsq
      nlinarith
    have hct : |center n (cycleCount c)-ordinaryLinearCenter θ n (cycleCount c)|≤Real.log (Real.log n) := by
      have he : center n (cycleCount c)-ordinaryLinearCenter θ n (cycleCount c)=
          center n (cycleCount c)-Real.log n*speed θ-ordinarySlope θ*((cycleCount c : Real)-θ*Real.log n) := by
        unfold ordinaryLinearCenter
        ring
      rw [he]
      exact ht.trans hr.le
    have ha := abs_sub_le (maximumLogModulus c) (center n (cycleCount c)) (ordinaryLinearCenter θ n (cycleCount c))
    exact False.elim (by linarith [le_of_not_gt h1])
  apply squeeze_zero' (Eventually.of_forall (fun n => ewensProbability_nonneg θ hθ n _)) hupper
  simpa only [add_zero] using (hcenter.add hcount).add htail

#print axioms ordinary_ewens_random_centering
end ConditionalSpectralExtremes
