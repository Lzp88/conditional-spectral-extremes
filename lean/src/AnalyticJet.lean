import Mathlib

/-! Actual analytic remainder identities used to justify finite coefficient truncations. -/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.ReservoirAnalysis

/-- Actual Taylor coefficient at the origin, shared by reservoir and marker saddle proofs. -/
def analyticCoefficient (f : Complex → Complex) (N : Nat) : Complex :=
  iteratedDeriv N f 0 / (N.factorial : Complex)

theorem analyticCoefficient_cexp (N : Nat) :
    analyticCoefficient Complex.exp N = 1 / (N.factorial : Complex) := by
  unfold analyticCoefficient
  rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
  simp

/-- Equality through degree `N-1`, expressed as an actual analytic remainder. -/
def SameJet (N : Nat) (f g : Complex → Complex) : Prop :=
  AnalyticAt Complex f 0 ∧ AnalyticAt Complex g 0 ∧
    ∃ r : Complex → Complex, AnalyticAt Complex r 0 ∧
      ∀ᶠ z in 𝓝 0, f z = g z + z ^ N * r z

theorem SameJet.refl (N : Nat) {f : Complex → Complex} (hf : AnalyticAt Complex f 0) :
    SameJet N f f := by
  refine ⟨hf, hf, 0, analyticAt_const, ?_⟩
  filter_upwards [] with z
  simp

theorem SameJet.symm {N : Nat} {f g : Complex → Complex} (h : SameJet N f g) : SameJet N g f := by
  obtain ⟨hf, hg, r, hr, he⟩ := h
  refine ⟨hg, hf, fun z => -r z, hr.neg, ?_⟩
  filter_upwards [he] with z hz
  linear_combination -hz

theorem SameJet.trans {N : Nat} {f g h : Complex → Complex}
    (hfg : SameJet N f g) (hgh : SameJet N g h) : SameJet N f h := by
  obtain ⟨hf, _, r, hr, he⟩ := hfg
  obtain ⟨_, hh, s, hs, he'⟩ := hgh
  refine ⟨hf, hh, fun z => r z + s z, hr.add hs, ?_⟩
  filter_upwards [he, he'] with z hz hz'
  linear_combination hz + hz'

theorem SameJet.add {N : Nat} {f₁ g₁ f₂ g₂ : Complex → Complex}
    (h₁ : SameJet N f₁ g₁) (h₂ : SameJet N f₂ g₂) :
    SameJet N (fun z => f₁ z + f₂ z) (fun z => g₁ z + g₂ z) := by
  obtain ⟨hf₁, hg₁, r₁, hr₁, he₁⟩ := h₁
  obtain ⟨hf₂, hg₂, r₂, hr₂, he₂⟩ := h₂
  refine ⟨hf₁.add hf₂, hg₁.add hg₂, fun z => r₁ z + r₂ z, hr₁.add hr₂, ?_⟩
  filter_upwards [he₁, he₂] with z hz₁ hz₂
  linear_combination hz₁ + hz₂

theorem SameJet.mul {N : Nat} {f₁ g₁ f₂ g₂ : Complex → Complex}
    (h₁ : SameJet N f₁ g₁) (h₂ : SameJet N f₂ g₂) :
    SameJet N (fun z => f₁ z * f₂ z) (fun z => g₁ z * g₂ z) := by
  obtain ⟨hf₁, hg₁, r₁, hr₁, he₁⟩ := h₁
  obtain ⟨hf₂, hg₂, r₂, hr₂, he₂⟩ := h₂
  refine ⟨hf₁.mul hf₂, hg₁.mul hg₂, fun z => r₁ z * f₂ z + g₁ z * r₂ z,
    (hr₁.mul hf₂).add (hg₁.mul hr₂), ?_⟩
  filter_upwards [he₁, he₂] with z hz₁ hz₂
  linear_combination f₂ z * hz₁ + g₁ z * hz₂

theorem SameJet.const_mul {N : Nat} {f g : Complex → Complex}
    (h : SameJet N f g) (c : Complex) :
    SameJet N (fun z => c * f z) (fun z => c * g z) :=
  (SameJet.refl N (analyticAt_const (v := c))).mul h

theorem SameJet.iteratedDeriv_eq {N : Nat} {f g : Complex → Complex}
    (h : SameJet N f g) (k : Nat) (hk : k < N) :
    iteratedDeriv k f 0 = iteratedDeriv k g 0 := by
  obtain ⟨hf, hg, r, hr, he⟩ := h
  have hfg : AnalyticAt Complex (fun z => f z - g z) 0 := hf.sub hg
  have ho : (N : ENat) ≤ analyticOrderAt (fun z => f z - g z) 0 :=
    (natCast_le_analyticOrderAt hfg).2 ⟨r, hr, by
      filter_upwards [he] with z hz
      simp only [sub_zero, smul_eq_mul]
      linear_combination hz⟩
  have hd := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfg).1 ho k hk
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt] at hd
  exact sub_eq_zero.mp hd

theorem SameJet.coefficient_eq {N : Nat} {f g : Complex → Complex}
    (h : SameJet N f g) (k : Nat) (hk : k < N) :
    iteratedDeriv k f 0 / (k.factorial : Complex) = iteratedDeriv k g 0 / (k.factorial : Complex) := by
  rw [h.iteratedDeriv_eq k hk]

theorem SameJet.analyticCoefficient_eq {N : Nat} {f g : Complex → Complex}
    (h : SameJet N f g) (k : Nat) (hk : k < N) :
    analyticCoefficient f k = analyticCoefficient g k := h.coefficient_eq k hk

theorem SameJet.sum {ι : Type*} (s : Finset ι) {N : Nat} {f g : ι → Complex → Complex}
    (h : ∀ i ∈ s, SameJet N (f i) (g i)) :
    SameJet N (fun z => ∑ i ∈ s, f i z) (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SameJet.refl N (analyticAt_const (v := (0 : Complex)))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem SameJet.prod {ι : Type*} (s : Finset ι) {N : Nat} {f g : ι → Complex → Complex}
    (h : ∀ i ∈ s, SameJet N (f i) (g i)) :
    SameJet N (fun z => ∏ i ∈ s, f i z) (fun z => ∏ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SameJet.refl N (analyticAt_const (v := (1 : Complex)))
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem SameJet.cexp {N : Nat} {f g : Complex → Complex} (h : SameJet N f g) :
    SameJet N (fun z => Complex.exp (f z)) (fun z => Complex.exp (g z)) := by
  obtain ⟨hf, hg, r, hr, he⟩ := h
  by_cases hN : N = 0
  · subst N
    refine ⟨hf.cexp, hg.cexp, fun z => Complex.exp (f z) - Complex.exp (g z),
      hf.cexp.sub hg.cexp, ?_⟩
    filter_upwards [] with z
    simp
  have hzero : f 0 - g 0 = 0 := by
    have hh := he.self_of_nhds
    simpa only [zero_pow hN, zero_mul, add_zero, sub_eq_zero] using hh
  have hq : AnalyticAt Complex (fun z => f z - g z) 0 := hf.sub hg
  have hexa : AnalyticAt Complex Complex.exp 0 := by fun_prop
  obtain ⟨F, hF, hFe⟩ := hexa.exists_eventuallyEq_sum_add_pow_mul 1
  have hFsimple : ∀ᶠ w in 𝓝 (0 : Complex), Complex.exp w = 1 + w * F w := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      iteratedDeriv_zero, Complex.exp_zero, smul_eq_mul, one_mul, pow_one] using hFe
  have hqc : Tendsto (fun z => f z - g z) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, hzero] using hq.continuousAt
  have hFc : AnalyticAt Complex (fun z => F (f z - g z)) 0 := by
    apply AnalyticAt.comp _ hq
    simpa only [hzero] using hF
  refine ⟨hf.cexp, hg.cexp, fun z => Complex.exp (g z) * r z * F (f z - g z),
    (hg.cexp.mul hr).mul hFc, ?_⟩
  filter_upwards [he, hqc.eventually hFsimple] with z hz hFz
  have hez : Complex.exp (f z) = Complex.exp (g z) * Complex.exp (f z - g z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hez, hFz]
  linear_combination Complex.exp (g z) * F (f z - g z) * hz

theorem SameJet.comp_of_zero {N : Nat} {f g p : Complex → Complex}
    (h : SameJet N f g) (hp : AnalyticAt Complex p 0) (hp0 : p 0 = 0) :
    SameJet N (fun z => f (p z)) (fun z => g (p z)) := by
  obtain ⟨hf, hg, r, hr, he⟩ := h
  have ho : (1 : ENat) ≤ analyticOrderAt p 0 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hp).2
    intro i hi
    have hi0 : i = 0 := by omega
    simpa only [hi0, iteratedDeriv_zero] using hp0
  obtain ⟨q, hq, hqe⟩ := (natCast_le_analyticOrderAt hp).1 ho
  have hpc : Tendsto p (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hp0] using hp.continuousAt
  have hfc : AnalyticAt Complex (fun z => f (p z)) 0 := by
    apply AnalyticAt.comp _ hp
    simpa only [hp0] using hf
  have hgc : AnalyticAt Complex (fun z => g (p z)) 0 := by
    apply AnalyticAt.comp _ hp
    simpa only [hp0] using hg
  have hrc : AnalyticAt Complex (fun z => r (p z)) 0 := by
    apply AnalyticAt.comp _ hp
    simpa only [hp0] using hr
  refine ⟨hfc, hgc, fun z => q z ^ N * r (p z), (hq.pow N).mul hrc, ?_⟩
  filter_upwards [hpc.eventually he, hqe] with z hz hqz
  simp only [sub_zero, pow_one, smul_eq_mul] at hqz
  calc
    f (p z) = g (p z) + p z ^ N * r (p z) := hz
    _ = g (p z) + z ^ N * (q z ^ N * r (p z)) := by
      rw [show p z ^ N = z ^ N * q z ^ N by rw [hqz, mul_pow]]
      ring

theorem SameJet.taylor (N : Nat) {f : Complex → Complex} (hf : AnalyticAt Complex f 0) :
    SameJet N f (fun z => ∑ i ∈ Finset.range N, analyticCoefficient f i * z ^ i) := by
  obtain ⟨r, hr, he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul N
  refine ⟨hf, by unfold analyticCoefficient; fun_prop, r, hr, ?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold analyticCoefficient
  ring

#print axioms SameJet.iteratedDeriv_eq
#print axioms SameJet.prod
#print axioms SameJet.cexp
#print axioms SameJet.comp_of_zero
#print axioms SameJet.taylor

end ConditionalSpectralExtremes.ReservoirAnalysis
