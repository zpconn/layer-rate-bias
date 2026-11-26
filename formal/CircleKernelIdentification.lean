module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import CircleSpectrum
public import Mathlib.Analysis.Fourier.AddCircle
import all CircleSpectrum
import all CircleAngularGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-! Direct identification of circle covariance and tangent spectra. We integrate
the overlap of two ReLU hemispheres in their actual polar angle. The readout
and radial second moments in the Gaussian initialization are respectively 1
and 2. Angles in [0,π] are the distances of two circle inputs. -/

public section
noncomputable section
namespace CircleKernelIdentification
open CircleSpectrum Real MeasureTheory Set

def gate (x : ℝ) : ℝ := if 0 < cos x then 1 else 0

/-- The angular covariance of two rectified features with radial moment 2. -/
def polarCov (s : ℝ) : ℝ :=
  (1/π) * ∫ t in -(π/2)..3*π/2, max (cos t) 0 * max (cos (t-s)) 0

/-- Angular hidden-Jacobian product. The two Cartesian components contribute
the input dot product cos(s) on the active intersection. -/
def polarHidden (s : ℝ) : ℝ :=
  1/(2*π) * ∫ t in -(π/2)..3*π/2, gate t * gate (t-s) * cos s

def polarNTK (τ s : ℝ) : ℝ := polarCov s + τ * polarHidden s

private theorem joint_active {s t : ℝ} (hs : 0 ≤ s) (hp : s ≤ π)
    (ht : t ∈ Ioo (-(π/2)) (3*π/2)) :
    (0 < cos t ∧ 0 < cos (t-s)) ↔ t ∈ Ioo (s-π/2) (π/2) := by
  constructor
  · intro ⟨h₁,h₂⟩
    constructor
    · by_contra! h
      have hn : cos (-(t-s)) ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith)
        (by linarith [ht.1])
      rw [cos_neg] at hn
      linarith
    · by_contra! h
      exact h₁.not_ge (cos_nonpos_of_pi_div_two_le_of_le h (by linarith [ht.2]))
  · intro ⟨h₁,h₂⟩
    exact ⟨cos_pos_of_mem_Ioo ⟨ht.1,h₂⟩, cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩⟩

/-- The zero-at-kink gates retain precisely the active intersection, up to the
endpoints of the integration interval. -/
theorem joint_gate_integral (s : ℝ) (hs : 0 ≤ s) (hp : s ≤ π) (f : ℝ → ℝ) :
    (∫ t in -(π/2)..3*π/2, gate t * gate (t-s) * f t) =
      ∫ t in s-π/2..π/2, f t := by
  let J := Ioo (-(π/2)) (3*π/2)
  let A := Ioo (s-π/2) (π/2)
  have sub : A ⊆ J := fun t ht => ⟨by linarith [ht.1],by linarith [ht.2, pi_pos]⟩
  rw [intervalIntegral.integral_of_le (by linarith [pi_pos]),
    intervalIntegral.integral_of_le (by linarith)]
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  change (∫ t in J, gate t * gate (t-s) * f t) = ∫ t in A, f t
  calc
    _ = ∫ t in J, A.indicator f t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      by_cases ha : t ∈ A
      · obtain ⟨h₁,h₂⟩ := (joint_active hs hp ht).mpr ha
        simp [gate, h₁, h₂, ha]
      · have hn := (joint_active hs hp ht).not.mpr ha
        by_cases h₁ : 0 < cos t
        · have h₂ : ¬ 0 < cos (t-s) := fun h => hn ⟨h₁,h⟩
          simp [gate, h₂, ha]
        · simp [gate, h₁, ha]
    _ = _ := by rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr sub]

private theorem relu_eq_gate (t : ℝ) : max (cos t) 0 = gate t * cos t := by
  by_cases h : 0 < cos t
  · simp [gate, h, max_eq_left h.le]
  · simp [gate, h, max_eq_right (le_of_not_gt h)]

theorem angular_covariance (s : ℝ) (hs : 0 ≤ s) (hp : s ≤ π) :
    polarCov s = (sin s+(π-s)*cos s)/(2*π) := by
  have hf (t : ℝ) : max (cos t) 0 * max (cos (t-s)) 0 =
      gate t * gate (t-s) * (cos t*cos (t-s)) := by simp_rw [relu_eq_gate]; ring
  unfold polarCov
  simp_rw [hf]
  rw [joint_gate_integral s hs hp]
  let F (t : ℝ) := t * cos s/2 + sin (2*t-s)/4
  have hF (t : ℝ) : HasDerivAt F (cos t * cos (t-s)) t := by
    have hi : HasDerivAt (fun x : ℝ => 2*x-s) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const s
    have h := ((((hasDerivAt_id t).mul_const (cos s)).div_const 2).add (hi.sin.div_const 4))
    change HasDerivAt (fun x : ℝ => x*cos s/2+sin (2*x-s)/4) _ t
    apply h.congr_deriv
    have hcos := two_mul_cos_mul_cos t (t-s)
    rw [show t+(t-s) = 2*t-s by ring, show t-(t-s)=s by ring] at hcos
    linear_combination -hcos / 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((continuous_cos.mul (continuous_cos.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
  dsimp [F]
  rw [show 2*(π/2)-s = π-s by ring, show 2*(s-π/2)-s=s-π by ring,
    sin_pi_sub, sin_sub_pi]
  ring

theorem angular_hidden (s : ℝ) (hs : 0 ≤ s) (hp : s ≤ π) :
    polarHidden s = (π-s)*cos s/(2*π) := by
  unfold polarHidden
  rw [joint_gate_integral s hs hp, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem angular_tangent (τ s : ℝ) (hs : 0 ≤ s) (hp : s ≤ π) :
    polarNTK τ s = (sin s+(1+τ)*(π-s)*cos s)/(2*π) := by
  rw [polarNTK, angular_covariance s hs hp, angular_hidden s hs hp]
  ring

/-- Cosine Fourier coefficient with the normalization for an even distance kernel. -/
def kernelCoeff (K : ℝ → ℝ) (k : ℝ) : ℝ := (1/π) * ∫ s in (0:ℝ)..π, K s*cos (k*s)

private theorem sine_primitive (a : ℝ) (ha : a ≠ 0) :
    (∫ s in (0:ℝ)..π, sin (a*s)) = (1-cos (a*π))/a := by
  simp_rw [mul_comm a _]
  rw [intervalIntegral.integral_comp_mul_right _ ha, integral_sin]
  simp [div_eq_inv_mul, mul_comm π a]

private theorem weighted_cos_integral (a : ℝ) (ha : a ≠ 0) :
    (∫ x in (0:ℝ)..π, (π-x)*cos (a*x)) = (1-cos (a*π))/a^2 := by
  let F (x : ℝ) := (π-x)*sin (a*x)/a - cos (a*x)/a^2
  have hd (t : ℝ) : HasDerivAt F ((π-t)*cos (a*t)) t := by
    have hax : HasDerivAt (fun x : ℝ => a*x) a t := by simpa using (hasDerivAt_id t).const_mul a
    have hπ : HasDerivAt (fun x : ℝ => π-x) (-1) t := by simpa using (hasDerivAt_id t).const_sub π
    convert (((hπ.mul hax.sin).div_const a).sub (hax.cos.div_const (a^2))) using 1
    field_simp [ha]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [F]
  ring

private theorem product_formula (τ k : ℝ) :
    kernelCoeff (polarNTK τ) k =
      ((∫ s in (0:ℝ)..π, sin ((1+k)*s)) + (∫ s in (0:ℝ)..π, sin ((1-k)*s)) +
       (1+τ)*((∫ s in (0:ℝ)..π, (π-s)*cos ((1+k)*s)) +
              (∫ s in (0:ℝ)..π, (π-s)*cos ((1-k)*s)))) / (4*π^2) := by
  have he : (∫ s in (0:ℝ)..π, polarNTK τ s * cos (k*s)) =
      ∫ s in (0:ℝ)..π, (1/(4*π))*
        ((sin ((1+k)*s) + sin ((1-k)*s)) +
         (1+τ)*((π-s)*cos ((1+k)*s)+(π-s)*cos ((1-k)*s))) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le pi_pos.le]
    intro s hs
    dsimp only
    rw [angular_tangent _ _ hs.1 hs.2]
    have h₁ := two_mul_sin_mul_cos s (k*s)
    have h₂ := two_mul_cos_mul_cos s (k*s)
    rw [show (1+k)*s = s+k*s by ring, show (1-k)*s=s-k*s by ring]
    rw [add_comm (sin (s+k*s)) _, ← h₁, ← mul_add, add_comm (cos (s+k*s)) _, ← h₂]
    ring
  rw [kernelCoeff, he, intervalIntegral.integral_const_mul]
  have hi (a : ℝ) : IntervalIntegrable (fun s : ℝ => sin (a*s)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  have hc (a : ℝ) : IntervalIntegrable (fun s : ℝ => (π-s)*cos (a*s)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add ((hi _).add (hi _)) (((hc _).add (hc _)).const_mul _),
    intervalIntegral.integral_add (hi _) (hi _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hc _) (hc _)]
  ring

private theorem signed_endpoint (j : ℕ) :
    cos ((1+2*(j:ℝ))*π) = -1 ∧ cos ((1-2*(j:ℝ))*π) = -1 := by
  rw [show (1+2*(j:ℝ))*π = π+j*(2*π) by ring, show (1-2*(j:ℝ))*π = π-j*(2*π) by ring]
  simp

/-- Every nonnegative even Fourier frequency of the angular tangent kernel. -/
theorem tangent_even (τ : ℝ) (j : ℕ) :
    kernelCoeff (polarNTK τ) (2*(j:ℝ)) = ntkEven τ (2*(j:ℝ)) := by
  have hp : 1 + 2*(j:ℝ) ≠ 0 := by positivity
  have hm : 1 - 2*(j:ℝ) ≠ 0 := by
    cases j with
    | zero => norm_num
    | succ j => push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [product_formula, sine_primitive _ hp, sine_primitive _ hm,
    weighted_cos_integral _ hp, weighted_cos_integral _ hm, (signed_endpoint j).1, (signed_endpoint j).2]
  unfold ntkEven
  rw [show (2*(j:ℝ))^2-1 = -(1-2*(j:ℝ))*(1+2*(j:ℝ)) by ring]
  field_simp [hp,hm,Real.pi_ne_zero]
  ring

theorem covariance_even (j : ℕ) :
    kernelCoeff polarCov (2*(j:ℝ)) = covEven (2*(j:ℝ)) := by
  have h : polarNTK 0 = polarCov := by funext s; simp [polarNTK]
  simpa [h,ntkEven,covEven] using tangent_even 0 j

/-- All higher odd Fourier frequencies vanish. -/
theorem tangent_odd_high (τ : ℝ) (j : ℕ) :
    kernelCoeff (polarNTK τ) (2*(j:ℝ)+3) = 0 := by
  have hp : 1 + (2*(j:ℝ)+3) ≠ 0 := by positivity
  have hm : 1 - (2*(j:ℝ)+3) ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [product_formula, sine_primitive _ hp, sine_primitive _ hm,
    weighted_cos_integral _ hp, weighted_cos_integral _ hm,
    show (1+(2*(j:ℝ)+3))*π = ((j+2:ℕ):ℝ)*(2*π) by push_cast; ring,
    show (1-(2*(j:ℝ)+3))*π = -(((j+1:ℕ):ℝ)*(2*π)) by push_cast; ring,
    cos_neg, cos_nat_mul_two_pi, cos_nat_mul_two_pi]
  simp

theorem tangent_one (τ : ℝ) : kernelCoeff (polarNTK τ) 1 = (1+τ)/8 := by
  have hi : (∫ x in (0:ℝ)..π, π-x) = π^2/2 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const, integral_id]
    simp [smul_eq_mul]
    ring
  rw [product_formula]
  norm_num only
  rw [sine_primitive _ (by norm_num), weighted_cos_integral _ (by norm_num)]
  simp [Real.cos_two_mul, hi]
  field_simp [Real.pi_ne_zero]
  ring

/-- Extend the angular-distance expression evenly. On [-π,π] this is the
periodic kernel as a function of signed displacement. -/
def distanceFormula (τ x : ℝ) : ℝ :=
  (sin x+(1+τ)*(π-x)*cos x)/(2*π)

theorem distanceFormula_agrees (τ : ℝ) {x : ℝ} (hx : |x| ≤ π) :
    distanceFormula τ |x| = polarNTK τ |x| :=
  (angular_tangent τ _ (abs_nonneg _) hx).symm

/-- Fourier reduction for an arbitrary continuous even distance profile. The
left side uses mathlib's complex Fourier coefficient on the full period. -/
theorem fourier_even_profile (f : ℝ → ℝ) (hf : Continuous f) (k : ℤ) :
    fourierCoeffOn (show -π < π by linarith [pi_pos]) (fun x => (f |x| : ℂ)) k =
      (kernelCoeff f k : ℂ) := by
  let e (x : ℝ) : ℂ := Complex.exp ((-(k:ℂ)*x)*Complex.I) * (f |x| : ℂ)
  have ec : Continuous e := by unfold e; fun_prop
  have idx (x : ℝ) : fourier (-k) (x : AddCircle (π - -π)) • (f |x| : ℂ) = e x := by
    rw [fourier_coe_apply, smul_eq_mul]
    unfold e
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [fourierCoeffOn_eq_integral]
  simp_rw [idx]
  have he (x : ℝ) (hx : 0 ≤ x) :
      e (-x) + e x = 2*(↑(f x*cos ((k:ℝ)*x)) : ℂ) := by
    unfold e
    rw [abs_neg, abs_of_nonneg hx]
    push_cast
    rw [show -(k:ℂ)*-(x:ℂ) = ↑((k:ℝ)*x) by push_cast; ring,
      show -(k:ℂ)*(x:ℂ) = ↑(-((k:ℝ)*x)) by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    ring
  have fold : (∫ s in -π..π, e s) = 2*↑(∫ x in (0:ℝ)..π, f x*cos (k*x)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (ec.intervalIntegrable (-π) 0) (ec.intervalIntegrable 0 π)]
    have hn := @intervalIntegral.integral_comp_neg ℂ _ _ 0 π e
    rw [neg_zero] at hn
    have hneg : IntervalIntegrable (fun x : ℝ => e (-x)) volume 0 π :=
      (ec.comp continuous_neg).intervalIntegrable _ _
    rw [← hn, ← intervalIntegral.integral_add hneg (ec.intervalIntegrable 0 π)]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le pi_pos.le]
    exact fun t ht => he t ht.1
  rw [fold, kernelCoeff, Complex.real_smul]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- The full-period, complex, normalized Fourier coefficients of the polar gradient kernel. -/
def tangentFourier (τ : ℝ) (k : ℤ) : ℂ :=
  fourierCoeffOn (show -π < π by linarith [pi_pos]) (fun x => (polarNTK τ |x| : ℂ)) k

theorem tangentFourier_eq (τ : ℝ) (k : ℤ) : tangentFourier τ k = (kernelCoeff (polarNTK τ) k : ℂ) := by
  have hp : -π < π := by linarith [pi_pos]
  have hae : (fun x => (polarNTK τ |x| : ℂ)) =ᵐ[volume.restrict (Ioc (-π) π)]
      (fun x => (distanceFormula τ |x| : ℂ)) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hx
    rw [distanceFormula_agrees τ (abs_le.mpr ⟨hx.1.le,hx.2⟩)]
  unfold tangentFourier
  rw [fourierCoeffOn_congr_ae hp hae, fourier_even_profile _ (by unfold distanceFormula; fun_prop)]
  congr 1
  unfold kernelCoeff
  congr 1
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le pi_pos.le]
  intro x hx
  dsimp only
  rw [angular_tangent τ x hx.1 hx.2]
  rfl

theorem tangentFourier_even (τ : ℝ) (j : ℕ) :
    tangentFourier τ (2*(j:ℤ)) = (ntkEven τ (2*(j:ℝ)) : ℂ) := by
  rw [tangentFourier_eq]; push_cast; rw [tangent_even]

/-- The stored interpolation weight is exactly the ratio of the actual polar
Fourier zero mode to its even aliases at k=2(n+1)(j+1). These are all nonzero
constant-mode aliases when N=n+1 is odd and at least three. -/
theorem weight_from_kernel (τ : ℝ) (n : ℕ) :
    weight τ n = kernelCoeff (polarNTK τ) 0 /
      (kernelCoeff (polarNTK τ) 0 + ∑' j : ℕ, 2*kernelCoeff (polarNTK τ) (2*((n:ℝ)+1)*((j:ℝ)+1))) := by
  have hzero : kernelCoeff (polarNTK τ) 0 = k0 τ := by
    simpa [ntkEven,k0] using tangent_even τ 0
  have halias (j : ℕ) : kernelCoeff (polarNTK τ) (2*((n:ℝ)+1)*((j:ℝ)+1)) =
      ntkEven τ (2*((n:ℝ)+1)*((j:ℝ)+1)) := by
    have h := tangent_even τ ((n+1)*(j+1))
    push_cast at h
    simpa only [mul_assoc] using h
  simp_rw [hzero, halias, weight, U_eq_alias_sum]

private theorem coeff_at_natAbs (f : ℝ → ℝ) (k : ℤ) :
    kernelCoeff f k = kernelCoeff f k.natAbs := by
  cases k with
  | ofNat n => rfl
  | negSucc n =>
    have hn : ((Int.negSucc n:ℤ):ℝ) = -((n:ℝ)+1) := by simp [Int.cast_negSucc]
    rw [hn]; simp only [Int.natAbs_negSucc, Nat.cast_succ, kernelCoeff, neg_mul, cos_neg]

private theorem ntk_at_natAbs (τ : ℝ) (k : ℤ) :
    ntkEven τ k = ntkEven τ k.natAbs := by
  cases k with
  | ofNat n => rfl
  | negSucc n => simp [ntkEven, Int.cast_negSucc]; ring

/-- Full Fourier sequence of the hidden-rate tangent kernel at every signed integer. -/
theorem tangentFourier_piecewise (τ : ℝ) (k : ℤ) :
    tangentFourier τ k = ((if Even k then ntkEven τ (k:ℝ)
      else if k.natAbs=1 then (1+τ)/8 else 0 : ℝ) : ℂ) := by
  rw [tangentFourier_eq, coeff_at_natAbs, ntk_at_natAbs]
  by_cases h : Even k
  · rw [ite_eq_left h]
    obtain ⟨j,hj⟩ := h.natAbs
    rw [hj]; push_cast
    simpa only [two_mul] using congrArg (fun x : ℝ => (x:ℂ)) (tangent_even τ j)
  · rw [ite_eq_right h]
    by_cases hone : k.natAbs = 1
    · rw [ite_eq_left hone, hone, Nat.cast_one, tangent_one]
    · rw [ite_eq_right hone]
      have ho : Odd k.natAbs := Nat.not_even_iff_odd.mp (fun hu => h (Int.natAbs_even.mp hu))
      obtain ⟨i,hi⟩ := ho
      cases i with
      | zero => simp_all
      | succ j =>
        have hj : k.natAbs = 2*j+3 := by omega
        rw [hj]; push_cast
        rw [tangent_odd_high, Complex.ofReal_zero]

open ProbabilityTheory

private theorem radial_one :
    (∫ r in Ioi (0:ℝ), r * exp (-(1/2)*r^2)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_two, Real.Gamma_one] at h
  simpa only [neg_mul] using h

private theorem radial_three :
    (∫ r in Ioi (0:ℝ), r^3 * exp (-(1/2)*r^2)) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=3) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hγ : Real.Gamma 2 = 1 := by simp
  norm_num [Real.rpow_two, hγ] at h
  simpa only [neg_mul] using h

/-- Integrate a separable polar pullback against two standard-normal densities. -/
private theorem gaussian_polar_separate (F : ℝ × ℝ → ℝ) (R A : ℝ → ℝ)
    (hF : ∀ r > 0, ∀ t : ℝ, F (r*cos t, r*sin t) = R r*A t) :
    (∫ p : ℝ × ℝ, (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2) * F p) =
      (1/(2*π))*(∫ r in Ioi (0:ℝ), r*exp (-(1/2)*r^2)*R r) *
      (∫ t in Ioo (-π) π, A t) := by
  rw [← integral_comp_polarCoord_symm]
  have hfun : (∫ p in polarCoord.target, p.1 •
      ((gaussianPDFReal 0 1 (polarCoord.symm p).1 * gaussianPDFReal 0 1 (polarCoord.symm p).2)*F (polarCoord.symm p))) =
      ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-π) π, (1/(2*π))*(p.1*exp (-(1/2)*p.1^2)*R p.1) * A p.2 := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r,t⟩ ht
    change r * ((gaussianPDFReal 0 1 (r*cos t) * gaussianPDFReal 0 1 (r*sin t)) * F (r*cos t,r*sin t)) = _
    rw [hF r ht.1 t, gaussianPDFReal, gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have h_sq : (r*cos t)^2 + (r*sin t)^2 = r^2 := by
      linear_combination r^2*(sin_sq_add_cos_sq t)
    have hh : -(r*cos t)^2/2 + -(r*sin t)^2/2 = -(1/2)*r^2 := by linarith
    have hg := Real.sq_sqrt (show 0 ≤ 2*π by positivity)
    rw [mul_mul_mul_comm (√(2*π))⁻¹ (exp _) (√(2*π))⁻¹ (exp _), ← Real.exp_add, hh, ← mul_inv, ← sq, hg]
    ring
  rw [hfun, MeasureTheory.Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => (1/(2*π))*(r*exp (-(1/2)*r^2)*R r)) A]
  rw [integral_const_mul]

def standardPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardPair := by unfold standardPair; infer_instance

private theorem standardPair_integral (F : ℝ × ℝ → ℝ) :
    (∫ p, F p ∂standardPair) = ∫ p : ℝ × ℝ, (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2)*F p := by
  rw [standardPair, gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1:NNReal) ≠ 0),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) _ F, Measure.volume_eq_prod]
  · simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul]
  · exact ae_of_all _ (fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)

private theorem angular_period (A : ℝ → ℝ) (hp : Function.Periodic A (2*π)) :
    (∫ t in Ioo (-π) π, A t) = ∫ t in -(π/2)..3*π/2, A t := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  simpa only [show -π + 2*π = π by ring, show -(π/2)+2*π = 3*π/2 by ring] using hp.intervalIntegral_add_eq (-π) (-(π/2))

/-- The covariance at two angles from the actual product of two independent
standard normal Cartesian hidden coordinates. The independent scalar readout
has second moment one. -/
def gaussianCov (s : ℝ) : ℝ :=
  ∫ w, max w.1 0 * max (w.1*cos s + w.2*sin s) 0 ∂standardPair

theorem gaussian_covariance_eq_polar (s : ℝ) : gaussianCov s = polarCov s := by
  let A (t : ℝ) := max (cos t) 0 * max (cos (t-s)) 0
  have hp : Function.Periodic A (2*π) := by
    intro x
    simp [A, show x+2*π-s = x-s+2*π by ring]
  rw [gaussianCov, standardPair_integral]
  rw [gaussian_polar_separate _ (fun r => r^2) A]
  · have h : (∫ r in Ioi (0:ℝ), r*exp (-(1/2)*r^2)*r^2) = 2 := by
      simp_rw [show ∀ r : ℝ, r*exp (-(1/2)*r^2)*r^2 = r^3*exp (-(1/2)*r^2) by intro r; ring]
      exact radial_three
    rw [h, angular_period _ hp, polarCov]
    dsimp [A]
    ring
  · intro r hr t
    dsimp only [A,Prod.fst,Prod.snd]
    rw [show r*cos t*cos s + r*sin t*sin s = r*cos (t-s) by rw [cos_sub]; ring]
    have hmax (a : ℝ) : max (r*a) 0 = r*max a 0 := by rw [mul_max_of_nonneg _ _ hr.le, mul_zero]
    rw [hmax, hmax]
    ring

private def scalarGate (x : ℝ) : ℝ := if 0 < x then 1 else 0

def gaussianHidden (s : ℝ) : ℝ :=
  ∫ z : ℝ × (ℝ × ℝ), z.1^2 * (scalarGate z.2.1 * scalarGate (z.2.1*cos s+z.2.2*sin s) * cos s)
    ∂(gaussianReal 0 1).prod standardPair

private theorem gaussian_second : (∫ a : ℝ, a^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (X:=fun x : ℝ => x) measurable_id.aemeasurable] at h
  simpa using h

theorem gaussian_hidden_eq_polar (s : ℝ) : gaussianHidden s = polarHidden s := by
  let A (t : ℝ) := gate t * gate (t-s)*cos s
  have hp : Function.Periodic A (2*π) := by
    intro x
    simp [A,gate,show x+2*π-s=x-s+2*π by ring]
  rw [gaussianHidden, integral_prod_mul (fun a : ℝ => a^2)
    (fun w : ℝ×ℝ => scalarGate w.1 * scalarGate (w.1*cos s+w.2*sin s) * cos s), gaussian_second, one_mul, standardPair_integral]
  rw [gaussian_polar_separate _ (fun _ => 1) A]
  · simp only [mul_one, radial_one, angular_period _ hp]
    rfl
  · intro r hr t
    dsimp only [A, Prod.fst, Prod.snd, one_mul, scalarGate, gate]
    rw [show r*cos t*cos s + r*sin t*sin s = r*cos (t-s) by rw [cos_sub]; ring]
    simp [mul_pos_iff_of_pos_left hr]

/-- The covariance of two actual randomly initialized neuron outputs, under
the product law of all three independent Gaussian coordinates. -/
theorem neuron_covariance (s : ℝ) :
    covariance (fun z : ℝ × (ℝ × ℝ) => z.1*max z.2.1 0)
      (fun z => z.1*max (z.2.1*cos s+z.2.2*sin s) 0)
      ((gaussianReal 0 1).prod standardPair) = polarCov s := by
  have mean (F : ℝ × ℝ → ℝ) :
      (∫ z, z.1 * F z.2 ∂(gaussianReal 0 1).prod standardPair) = 0 := by
    rw [integral_prod_mul (fun a : ℝ => a) F, integral_id_gaussianReal, zero_mul]
  rw [covariance, mean (fun w => max w.1 0), mean (fun w => max (w.1*cos s+w.2*sin s) 0)]
  simp only [sub_zero]
  simp_rw [show ∀ z : ℝ × (ℝ × ℝ), z.1*max z.2.1 0*(z.1*max (z.2.1*cos s+z.2.2*sin s) 0) =
    z.1^2 * (max z.2.1 0*max (z.2.1*cos s+z.2.2*sin s) 0) by intro z; ring]
  rw [integral_prod_mul (fun a : ℝ => a^2)
    (fun w : ℝ × ℝ => max w.1 0 * max (w.1*cos s + w.2*sin s) 0), gaussian_second, one_mul]
  exact gaussian_covariance_eq_polar s

/-- Cartesian independent-Gaussian gradient kernel has the piecewise circle spectrum. -/
theorem gaussian_kernel_fourier (τ : ℝ) (k : ℤ) :
    fourierCoeffOn (show -π < π by linarith [pi_pos])
      (fun x : ℝ => ((gaussianCov |x|+τ*gaussianHidden |x|:ℝ):ℂ)) k =
      ((if Even k then ntkEven τ (k:ℝ) else if k.natAbs=1 then (1+τ)/8 else 0 : ℝ) : ℂ) := by
  simp_rw [gaussian_covariance_eq_polar, gaussian_hidden_eq_polar]
  exact tangentFourier_piecewise τ k

/-- Projection of Cartesian hidden weights on a circle input at angle u. -/
def projection (u : ℝ) (w : ℝ × ℝ) := w.1*cos u + w.2*sin u

private theorem projection_polar (u t r : ℝ) :
    projection u (r*cos t,r*sin t) = r*cos (t-u) := by
  simp only [projection, cos_sub]
  ring

/-- Two possibly different circle inputs, with independent Gaussian hidden weights. -/
def cartesianProduct (F : ℝ → ℝ) (u v : ℝ) :=
  ∫ w, F (projection u w)*F (projection v w) ∂standardPair

private theorem rotate_product (F R : ℝ → ℝ)
    (hF : ∀ r > 0, ∀ x, F (r*x) = R r*F x) (u v : ℝ) :
    cartesianProduct F u v = cartesianProduct F 0 (v-u) := by
  let A (u v t : ℝ) := F (cos (t-u))*F (cos (t-v))
  have integral (u v : ℝ) : cartesianProduct F u v =
      1/(2*π) * (∫ r in Ioi (0:ℝ), r*exp (-(1/2)*r^2)*(R r)^2) * ∫ t in Ioo (-π) π, A u v t := by
    rw [cartesianProduct, standardPair_integral]
    apply gaussian_polar_separate
    intro r hr t
    dsimp only [A]
    rw [projection_polar, projection_polar, hF r hr, hF r hr]
    ring
  rw [integral, integral]
  congr 1
  have hp : Function.Periodic (A 0 (v-u)) (2*π) := by
    intro x
    simp [A, show x+2*π-(v-u) = x-(v-u)+2*π by ring]
  have hs (t : ℝ) : A u v t = A 0 (v-u) (t-u) := by simp [A, show t-u-(v-u)=t-v by ring]
  simp_rw [hs]
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
    ← intervalIntegral.integral_of_le (by linarith [pi_pos]), intervalIntegral.integral_comp_sub_right]
  simpa only [show -π-u+2*π = π-u by ring, show -π+2*π = π by ring] using
    hp.intervalIntegral_add_eq (-π-u) (-π)

private theorem rotate_product_abs (F R : ℝ → ℝ)
    (hF : ∀ r > 0, ∀ x, F (r*x) = R r*F x) (u v : ℝ) :
    cartesianProduct F u v = cartesianProduct F 0 |v-u| := by
  rcases le_or_gt u v with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), rotate_product F R hF]
  · rw [abs_of_neg (sub_neg.mpr h), neg_sub]
    rw [← rotate_product F R hF v u]
    unfold cartesianProduct
    simp only [mul_comm]

/-- Population tangent kernel of both sets of trainable parameters at arbitrary
circle inputs; the scalar readout's independent second moment is one. -/
def cartesianKernel (τ u v : ℝ) : ℝ :=
  cartesianProduct (fun x => max x 0) u v +
    τ * (cartesianProduct scalarGate u v * cos (v-u))

theorem cartesian_kernel_isotropic (τ u v : ℝ) :
    cartesianKernel τ u v = polarNTK τ |v-u| := by
  have hc (s : ℝ) : cartesianProduct (fun x => max x 0) 0 s = gaussianCov s := by
    simp [cartesianProduct,gaussianCov,projection]
  have hh (s : ℝ) : cartesianProduct scalarGate 0 s * cos s = gaussianHidden s := by
    rw [gaussianHidden, integral_prod_mul (fun a : ℝ => a^2)
      (fun w : ℝ×ℝ => scalarGate w.1 * scalarGate (w.1*cos s+w.2*sin s) * cos s), gaussian_second, one_mul,
      integral_mul_const]
    simp [cartesianProduct,projection]
  have hr (r : ℝ) (hr : 0 < r) (x : ℝ) : max (r*x) 0 = r*max x 0 := by
    rw [mul_max_of_nonneg _ _ hr.le, mul_zero]
  have hg (r : ℝ) (hr : 0 < r) (x : ℝ) : scalarGate (r*x) = 1*scalarGate x := by
    simp [scalarGate, mul_pos_iff_of_pos_left hr]
  rw [cartesianKernel, rotate_product_abs (fun x => max x 0) (fun r => r) hr,
    rotate_product_abs scalarGate (fun _ => 1) hg, hc, gaussian_covariance_eq_polar,
    ← cos_abs (v-u), hh, gaussian_hidden_eq_polar]
  rfl

/-- Per-unit continuous readout multiplier on the Cartesian Gaussian pair. -/
def populationFeature (w : ℝ × ℝ) := √(w.1^2+w.2^2)/π

private theorem pop_polar (r t : ℝ) (hr : 0 < r) :
    populationFeature (r*cos t,r*sin t) = r/π := by
  unfold populationFeature
  rw [show (r*cos t)^2+(r*sin t)^2=r^2 by linear_combination r^2*(sin_sq_add_cos_sq t), sqrt_sq hr.le]

private theorem weighted_radial_three :
    (∫ r in Ioi (0:ℝ), r*exp (-(1/2)*r^2)*r^2) = 2 := by
  simp_rw [show ∀ r : ℝ, r*exp (-(1/2)*r^2)*r^2 = r^3*exp (-(1/2)*r^2) by intro r; ring]
  exact radial_three

theorem populationFeature_second : (∫ w, populationFeature w^2 ∂standardPair) = c0 := by
  rw [standardPair_integral, gaussian_polar_separate _ (fun r => r^2) (fun _ => 1/π^2)]
  · rw [weighted_radial_three, setIntegral_const, Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [pi_pos])]
    simp only [c0,smul_eq_mul]
    field_simp [pi_ne_zero]; ring
  · intro r hr t; rw [pop_polar r t hr]; ring

theorem populationFeature_mixed (u : ℝ) :
    (∫ w, populationFeature w * max (projection u w) 0 ∂standardPair) = c0 := by
  rw [standardPair_integral, gaussian_polar_separate _ (fun r => r^2) (fun t => (1/π)*max (cos (t-u)) 0)]
  · rw [weighted_radial_three, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos])]
    have h : (∫ t in -π..π, max (cos (t-u)) 0) = 2 := by
      rw [intervalIntegral.integral_comp_sub_right (fun t => max (cos t) 0)]
      have hh := CircleAngularGeometry.integral_half (-π-u)
      simpa only [CircleAngularGeometry.halfWave, show -π-u+2*π=π-u by ring] using hh
    rw [h,c0]
    ring
  · intro r hr t
    have hmax (a : ℝ) : max (r*a) 0 = r*max a 0 := by rw [mul_max_of_nonneg _ _ hr.le, mul_zero]
    rw [pop_polar r t hr, projection_polar, hmax]
    ring

end CircleKernelIdentification
