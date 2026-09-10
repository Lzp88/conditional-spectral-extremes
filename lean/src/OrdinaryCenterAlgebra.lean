import CenterMinimizer

/-! Exact scaling of the speed's genuine quadratic remainder, preserving theta variance. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem scaled_speed_quadratic_bound (L k θ a C : Real) (hL : 0 < L) (hθ : 0 < θ)
    (h : |speed (k/L)-speed θ-a*(k/L-θ)|≤C*(k/L-θ)^2) :
    |L*speed (k/L)-L*speed θ-a*(k-θ*L)|≤
      C*θ*((k-θ*L)/Real.sqrt (θ*L))^2 := by
  have hs : Real.sqrt (θ*L) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hθ hL)).ne'
  have hsq := Real.sq_sqrt (mul_pos hθ hL).le
  have he1 : L*speed (k/L)-L*speed θ-a*(k-θ*L)=L*(speed (k/L)-speed θ-a*(k/L-θ)) := by
    field_simp
  rw [he1,abs_mul,abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left h hL.le).trans_eq
  rw [div_pow,hsq]
  field_simp

theorem actual_center_quadratic_bound (n k : Nat) (θ a C : Real) (hn : 1 < n)
    (hk : 0 < k) (hθ : 0 < θ)
    (h : |speed ((k : Real)/Real.log n)-speed θ-a*((k : Real)/Real.log n-θ)|≤
      C*((k : Real)/Real.log n-θ)^2) :
    |center n k-Real.log n*speed θ-a*((k : Real)-θ*Real.log n)|≤
      C*θ*(((k : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n))^2 := by
  rw [center_eq_speed hn hk]
  exact scaled_speed_quadratic_bound _ _ _ _ _ (Real.log_pos (by exact_mod_cast hn)) hθ h

#print axioms scaled_speed_quadratic_bound
#print axioms actual_center_quadratic_bound
end ConditionalSpectralExtremes
