module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! Normalized real Fourier coefficients of a half-wave and the two-sided alias
sums at the even multiples of a grid size. The latter describe odd grids of
size ≥ 3. Grid sizes and positive series indices are both enumerated by n+1. -/

public section
open Filter Topology Real MeasureTheory

namespace CircleSpectrum

noncomputable section

def halfWaveCoeff (k : ℝ) :=
  (∫ t in (0 : ℝ)..π / 2, cos t * cos (k*t)) / π

private theorem cosine_integral {k : ℝ} (h : k ≠ 0) :
    (∫ t in (0:ℝ)..π / 2, cos (t*k)) = sin (π/2*k) / k := by
  rw [intervalIntegral.integral_comp_mul_right _ h, integral_cos]
  simp [div_eq_inv_mul]

/-- Product-to-sum integral for every nonresonant frequency. -/
theorem halfWaveCoeff_formula (k : ℝ) (hm : k - 1 ≠ 0) (hp : k + 1 ≠ 0) :
    halfWaveCoeff k =
      (sin (π/2*(k-1))/(k-1) + sin (π/2*(k+1))/(k+1)) / (2*π) := by
  have hf (t : ℝ) : cos t * cos (k*t) =
      (1/2) * (cos (t*(k-1)) + cos (t*(k+1))) := by
    have h := two_mul_cos_mul_cos (k*t) t
    rw [show t*(k-1)=k*t-t by ring, show t*(k+1)=k*t+t by ring]
    linarith
  unfold halfWaveCoeff
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
    cosine_integral hm, cosine_integral hp]
  · ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem halfWaveCoeff_even (j : ℕ) :
    halfWaveCoeff (2*(j:ℝ)) = (-1:ℝ)^j / (π*(1-(2*(j:ℝ))^2)) := by
  have hm : 2*(j:ℝ)-1 ≠ 0 := by
    cases j with
    | zero => norm_num
    | succ j => push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hp : 2*(j:ℝ)+1 ≠ 0 := by positivity
  rw [halfWaveCoeff_formula _ hm hp,
    show π / 2 * (2 * (j:ℝ) - 1) = j*π - π/2 by ring,
    show π / 2 * (2 * (j:ℝ) + 1) = j*π + π/2 by ring,
    sin_sub_pi_div_two, sin_add_pi_div_two, cos_nat_mul_pi]
  rw [show 1-(2*(j:ℝ))^2 = -(2*(j:ℝ)-1)*(2*(j:ℝ)+1) by ring]
  field_simp [Real.pi_pos.ne', hm, hp]
  ring

theorem halfWaveCoeff_odd_high (j : ℕ) :
    halfWaveCoeff (2*(j:ℝ)+3) = 0 := by
  have hm : 2*(j:ℝ)+3-1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hp : 2*(j:ℝ)+3+1 ≠ 0 := by positivity
  rw [halfWaveCoeff_formula _ hm hp,
    show π/2*(2*(j:ℝ)+3-1) = ((j+1:ℕ):ℝ)*π by push_cast; ring,
    show π/2*(2*(j:ℝ)+3+1) = ((j+2:ℕ):ℝ)*π by push_cast; ring,
    sin_nat_mul_pi, sin_nat_mul_pi]
  simp

theorem halfWaveCoeff_one : halfWaveCoeff 1 = 1/4 := by
  have hf (t : ℝ) : cos t * cos (1*t) = 1/2 * (1+cos (t*2)) := by
    have h := two_mul_cos_mul_cos t t
    simp only [sub_self, cos_zero, one_mul] at *
    rw [show t*2=t+t by ring]
    linarith
  unfold halfWaveCoeff
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
    intervalIntegral.integral_const, cosine_integral (by norm_num : (2:ℝ) ≠ 0)]
  · simp
    field_simp
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Positive-index reciprocal powers, including the very first term j=0 (index 1). -/
def rp (p j : ℕ) : ℝ := 1/((j:ℝ)+1)^p

private theorem rp_two_sum : HasSum (rp 2) (π^2/6) := by
  change HasSum (fun j : ℕ => 1/((j:ℝ)+1)^2) _
  simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two

private theorem rp_four_sum : HasSum (rp 4) (π^4/90) := by
  change HasSum (fun j : ℕ => 1/((j:ℝ)+1)^4) _
  simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four

private theorem rp_two_zero : Tendsto (rp 2) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => 1/((j:ℝ)+1)^2) _ _
  simpa [div_pow] using
    ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).pow 2)

def offset (n j : ℕ) := rp 2 n * rp 2 j / 4

private theorem offset_bounds (n j : ℕ) : 0 ≤ offset n j ∧ offset n j ≤ 1/4 := by
  have h (i : ℕ) : 0 ≤ rp 2 i ∧ rp 2 i ≤ 1 := by
    unfold rp
    constructor
    · positivity
    · apply div_le_one_of_le₀ <;> nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg (i:ℝ)]
  constructor
  · exact div_nonneg (mul_nonneg (h n).1 (h j).1) (by norm_num)
  · unfold offset
    have := mul_le_mul (h n).2 (h j).2 (h j).1 (by norm_num : (0:ℝ) ≤ 1)
    linarith

private theorem offset_zero (j : ℕ) : Tendsto (fun n => offset n j) atTop (𝓝 0) := by
  simpa [offset] using (rp_two_zero.mul_const (rp 2 j)).div_const 4

/-- (N^2)U_N in positive-index form, N=n+1. -/
def scaledU (τ : ℝ) (n : ℕ) : ℝ :=
  (1/(2*π^2)) * ∑' j, (rp 2 j) *
    ((τ+(2+τ)*offset n j)/(1-offset n j)^2)

/-- (N^4)S_N in positive-index form, N=n+1. -/
def scaledS (n : ℕ) : ℝ :=
  (1/(4*π^2)) * ∑' j, rp 4 j * (1/(1-offset n j)^2)

theorem scaledU_limit (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (scaledU τ) atTop (𝓝 (τ / 12)) := by
  let f (n j : ℕ) := rp 2 j * ((τ+(2+τ)*offset n j)/(1-offset n j)^2)
  have hlim (j : ℕ) : Tendsto (fun n => f n j) atTop (𝓝 (τ * rp 2 j)) := by
    have h := offset_zero j
    unfold f
    rw [mul_comm τ (rp 2 j)]
    convert (tendsto_const_nhds (x := rp 2 j)).mul
      ((tendsto_const_nhds.add (h.const_mul (2+τ))).div
        ((tendsto_const_nhds.sub h).pow 2) (by norm_num : (1-(0:ℝ))^2 ≠ 0)) using 1
    simp
  have hnorm (n j : ℕ) : ‖f n j‖ ≤ (8*(τ+1)) * rp 2 j := by
    obtain ⟨h₀,h₁⟩ := offset_bounds n j
    have hz : 0 ≤ rp 2 j := by unfold rp; positivity
    have hd : (1/2:ℝ) ≤ (1-offset n j)^2 := by nlinarith [sq_nonneg (offset n j)]
    have hl : τ+(2+τ)*offset n j ≤ τ+(2+τ)*(1/4) :=
      add_le_add_right (mul_le_mul_of_nonneg_left h₁ (by linarith : 0 ≤ 2+τ)) _
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ f n j by unfold f; positivity), mul_comm (8*(τ+1)) _]
    apply mul_le_mul_of_nonneg_left _ hz
    apply (div_le_iff₀ (by linarith : 0 < (1-offset n j)^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 8*(τ+1))]
  have ht := tendsto_tsum_of_dominated_convergence
    (rp_two_sum.summable.mul_left (8*(τ+1))) hlim (Eventually.of_forall hnorm)
  have hs := (rp_two_sum.mul_left τ).tsum_eq
  rw [hs] at ht
  rw [show τ / 12 = (1/(2*π^2)) * (τ * (π^2/6)) by field_simp; ring]
  exact ht.const_mul _

theorem scaledS_limit : Tendsto scaledS atTop (𝓝 (π^2 / 360)) := by
  let f (n j : ℕ) := rp 4 j * (1/(1-offset n j)^2)
  have hlim (j : ℕ) : Tendsto (fun n => f n j) atTop (𝓝 (rp 4 j)) := by
    have h := offset_zero j
    unfold f
    convert (tendsto_const_nhds (x := rp 4 j)).mul
      (tendsto_const_nhds.div ((tendsto_const_nhds.sub h).pow 2)
        (by norm_num : (1-(0:ℝ))^2 ≠ 0)) using 1
    simp
  have hnorm (n j : ℕ) : ‖f n j‖ ≤ 2 * rp 4 j := by
    obtain ⟨_,h₁⟩ := offset_bounds n j
    have hd : (1/2:ℝ) ≤ (1-offset n j)^2 := by nlinarith [sq_nonneg (offset n j)]
    have hpos : 0 ≤ rp 4 j := by unfold rp; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ f n j by unfold f; positivity), mul_comm 2 _]
    apply mul_le_mul_of_nonneg_left _ hpos
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have ht := tendsto_tsum_of_dominated_convergence
    (rp_four_sum.summable.mul_left 2) hlim (Eventually.of_forall hnorm)
  rw [rp_four_sum.tsum_eq] at ht
  rw [show π^2 / 360 = (1/(4*π^2)) * (π^4/90) by field_simp; ring]
  exact ht.const_mul _

def k0 (τ : ℝ) := (2+τ)/π^2
def c0 : ℝ := 2/π^2
def U (τ : ℝ) (n : ℕ) := rp 2 n * scaledU τ n
def S (n : ℕ) := rp 4 n * scaledS n
def weight (τ : ℝ) (n : ℕ) := k0 τ/(k0 τ + U τ n)
def variance (τ : ℝ) (n : ℕ) :=
  c0 * (1-weight τ n)^2 + (weight τ n)^2 * S n

private theorem hpden (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) : 0 < k0 τ + U τ n := by
  apply add_pos_of_pos_of_nonneg (by unfold k0; positivity)
  unfold U scaledU
  apply mul_nonneg (by unfold rp; positivity)
  apply mul_nonneg (by positivity)
  apply tsum_nonneg
  intro j
  have hz := (offset_bounds n j).1
  unfold rp
  positivity

theorem weight_limit (τ : ℝ) (hτ : 0 ≤ τ) : Tendsto (weight τ) atTop (𝓝 1) := by
  have hk : k0 τ ≠ 0 := by unfold k0; positivity
  have hu : Tendsto (U τ) atTop (𝓝 0) := by
    change Tendsto (fun n => rp 2 n * scaledU τ n) _ _
    simpa using rp_two_zero.mul (scaledU_limit τ hτ)
  have h := (tendsto_const_nhds (x := k0 τ)).div
    (hu.const_add (k0 τ)) (by simpa using hk)
  change Tendsto (fun n => k0 τ / (k0 τ + U τ n)) _ _
  simpa [hk, Pi.div_def] using h

theorem bias_limit (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 * (1-weight τ n)) atTop
      (𝓝 (π^2*τ/(12*(2+τ)))) := by
  have hk : k0 τ ≠ 0 := by unfold k0; positivity
  have hu : Tendsto (U τ) atTop (𝓝 0) := by
    change Tendsto (fun n => rp 2 n * scaledU τ n) _ _
    simpa using rp_two_zero.mul (scaledU_limit τ hτ)
  have h := (scaledU_limit τ hτ).div (hu.const_add (k0 τ)) (by simpa using hk)
  have hfun (n : ℕ) : ((n:ℝ)+1)^2 * (1-weight τ n) = scaledU τ n / (k0 τ+U τ n) := by
    unfold weight
    field_simp [(hpden τ hτ n).ne']
    simp [U, rp]
    field_simp
  simp_rw [hfun]
  convert h using 2
  simp [k0]
  field_simp

theorem variance_limit (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^4 * variance τ n) atTop
      (𝓝 (π^2/360*(1+5*τ^2/(2+τ)^2))) := by
  have hfun (n : ℕ) : ((n:ℝ)+1)^4 * variance τ n =
      c0 * (((n:ℝ)+1)^2*(1-weight τ n))^2 + (weight τ n)^2 * scaledS n := by
    unfold variance S rp
    have h : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  simp_rw [hfun]
  have h := (((bias_limit τ hτ).pow 2).const_mul c0).add
    (((weight_limit τ hτ).pow 2).mul scaledS_limit)
  convert h using 2
  simp [c0]
  field_simp
  ring

theorem equal_rate_variance :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^4 * variance 1 n) atTop (𝓝 (7*π^2/1620)) := by
  convert variance_limit 1 (by norm_num) using 2
  ring


/-- Unscaled spectrum at even frequencies (the covariance formula also applies at zero). -/
def covEven (k : ℝ) := 2 / (π^2*(k^2-1)^2)
def ntkEven (τ k : ℝ) := (2+τ*(1+k^2))/(π^2*(k^2-1)^2)

/-- Turning the positive even cosine-integral frequencies into both spectra. -/
theorem even_coeff_spectra (τ : ℝ) (j : ℕ) :
    2 * (halfWaveCoeff (2*(j:ℝ)))^2 = covEven (2*(j:ℝ)) ∧
    (2 + τ*(1+(2*(j:ℝ))^2)) * (halfWaveCoeff (2*(j:ℝ)))^2 = ntkEven τ (2*(j:ℝ)) := by
  rw [halfWaveCoeff_even, div_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num
  unfold covEven ntkEven
  rw [show 1 - (2*(j:ℝ))^2 = -((2*(j:ℝ))^2-1) by ring]
  simp [mul_pow, mul_comm, div_eq_mul_inv]
  exact ⟨by ring, Or.inl (by ring)⟩

private theorem sub_offset (n j : ℕ) :
    1-offset n j = ((2*((n:ℝ)+1)*((j:ℝ)+1))^2-1)/(2*((n:ℝ)+1)*((j:ℝ)+1))^2 := by
  unfold offset rp
  field_simp
  ring

theorem U_eq_alias_sum (τ : ℝ) (n : ℕ) :
    U τ n = ∑' j : ℕ, 2 * ntkEven τ (2*((n:ℝ)+1)*((j:ℝ)+1)) := by
  unfold U scaledU
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [sub_offset]
  unfold rp offset ntkEven rp
  field_simp
  ring

theorem S_eq_alias_sum (n : ℕ) :
    S n = ∑' j : ℕ, 2 * covEven (2*((n:ℝ)+1)*((j:ℝ)+1)) := by
  unfold S scaledS
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [sub_offset]
  unfold rp covEven
  field_simp
  ring

def minVariance (n : ℕ) := c0*S n/(c0+S n)

theorem minVariance_limit :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^4 * minVariance n) atTop (𝓝 (π^2/360)) := by
  have hz : Tendsto (rp 4) atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => 1/((j:ℝ)+1)^4) _ _
    simpa [div_pow] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).pow 4)
  have hs : Tendsto (fun n => rp 4 n * scaledS n) atTop (𝓝 0) := by
    simpa using hz.mul scaledS_limit
  have hc : c0 ≠ 0 := by unfold c0; positivity
  have hfun (n : ℕ) : ((n:ℝ)+1)^4 * minVariance n = c0 * scaledS n / (c0+S n) := by
    unfold minVariance
    rw [← mul_div_assoc]
    congr 1
    unfold S rp
    field_simp
  simp_rw [hfun]
  have h := (scaledS_limit.const_mul c0).div (hs.const_add c0) (by simpa using hc)
  simpa [S, hc, Pi.div_def, mul_div_cancel_left₀] using h

theorem varianceRatio_limit (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => variance τ n / minVariance n) atTop
      (𝓝 (1+5*τ^2/(2+τ)^2)) := by
  have h := (variance_limit τ hτ).div minVariance_limit (by positivity)
  have hfun (n : ℕ) : (((n:ℝ)+1)^4 * variance τ n) / (((n:ℝ)+1)^4 * minVariance n) =
      variance τ n / minVariance n := mul_div_mul_left _ _ (by positivity)
  simpa [Pi.div_def, hfun, mul_div_cancel_left₀, Real.pi_ne_zero] using h

/-- Normalized angular grid sum of a character at any integer frequency. -/
theorem grid_character_mean {N : ℕ} [NeZero N] (k : ℤ) :
    (∑ i : ZMod N, ZMod.stdAddChar ((k : ZMod N)*i)) / (N : ℂ) =
      if (N : ℤ) ∣ k then 1 else 0 := by
  by_cases h : (k : ZMod N) = 0
  · have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd k N).mp h
    simp [hd, h, AddChar.map_zero_eq_one, ZMod.card, NeZero.ne (N:ℂ)]
  · have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd k N).not.mp h
    have sm : ∑ i : ZMod N, ZMod.stdAddChar ((k : ZMod N)*i) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)
    simp [hd, sm]

/-- Exact aliasing for an absolutely summable complex Fourier series on the grid. -/
theorem grid_series_mean {N : ℕ} [NeZero N] (a : ℤ → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    (∑ i : ZMod N, ∑' k : ℤ, a k * ZMod.stdAddChar ((k : ZMod N)*i)) / (N : ℂ) =
      ∑' k : ℤ, if (N : ℤ) ∣ k then a k else 0 := by
  have hsum (i : ZMod N) : Summable (fun k : ℤ => a k * ZMod.stdAddChar ((k : ZMod N)*i)) :=
    ha.of_norm_bounded (fun k => by simp [AddChar.norm_apply])
  rw [← Summable.tsum_finsetSum (fun i _ => hsum i), div_eq_mul_inv, ← tsum_mul_right]
  apply tsum_congr
  intro k
  rw [← Finset.mul_sum, mul_assoc, ← div_eq_mul_inv, grid_character_mean]
  split <;> simp

/-- Every row of a grid convolution sends the constant-one function to the
sum of the aliased coefficients in its constant Fourier mode. -/
theorem constant_mode_eigenvalue {N : ℕ} [NeZero N] (a : ℤ → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (i : ZMod N) :
    (∑ j : ZMod N, ∑' k : ℤ, a k * ZMod.stdAddChar ((k : ZMod N)*(i-j))) / (N : ℂ) =
      ∑' k : ℤ, if (N : ℤ) ∣ k then a k else 0 := by
  let F (d : ZMod N) := ∑' k : ℤ, a k * ZMod.stdAddChar ((k : ZMod N)*d)
  change (∑ j, F (i-j)) / _ = _
  rw [show (∑ j, F (i-j)) = ∑ j, F j from
    Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun _ => rfl)]
  exact grid_series_mean a ha


end
end CircleSpectrum
