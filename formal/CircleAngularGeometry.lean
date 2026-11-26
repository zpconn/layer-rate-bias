module

public import CircleGridMoments
import all CircleEscape
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Angular integration and finite-grid quadrature for the actual circle network. -/
public section
noncomputable section
namespace CircleAngularGeometry

open Real MeasureTheory CircleEscape
open scoped InnerProductSpace

def point (t : ℝ) : ℂ := ⟨cos t, sin t⟩

theorem projection (w : ℂ) (t : ℝ) : inner ℝ w (point t) = ‖w‖ * cos (t-w.arg) := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, cos_sub]
  dsimp [point]
  have h := Complex.norm_mul_cos_arg w
  have k := Complex.norm_mul_sin_arg w
  linear_combination -(cos t) * h - (sin t) * k

def halfWave (t : ℝ) : ℝ := max (cos t) 0

private theorem continuous_half : Continuous halfWave := continuous_cos.max continuous_const

private theorem half_period : Function.Periodic halfWave (2*π) := by
  intro x
  simp [halfWave, cos_add_two_pi]

theorem integral_half (a : ℝ) : ∫ t in a..a+2*π, halfWave t = 2 := by
  rw [half_period.intervalIntegral_add_eq a (-(π/2))]
  have h₁ : (∫ t in -(π/2)..π/2, halfWave t) = (∫ t in -(π/2)..π/2, cos t) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by linarith [pi_pos])]
    exact fun x hx => max_eq_left (cos_nonneg_of_mem_Icc hx)
  have h₂ : (∫ t in π/2..(-(π/2)+2*π), halfWave t) = (∫ _t in π/2..(-(π/2)+2*π), (0:ℝ)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by linarith [pi_pos])]
    exact fun x hx => max_eq_right (cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2]))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_half.intervalIntegrable (-(π/2)) (π/2)) (continuous_half.intervalIntegrable _ _),
    h₁,h₂,integral_cos]
  norm_num

theorem feature_eq (w : ℂ) (t : ℝ) : feature w (point t) = ‖w‖ * halfWave (t-w.arg) := by
  simp only [feature, projection, halfWave, mul_max_of_nonneg _ _ (norm_nonneg w), mul_zero]

theorem real_angular_mean (c : ℝ) {m : ℕ} (n : Net ℂ m) :
    (∫ t in 0..2*π, output c n (point t))/(2*π) = populationMean c n := by
  have hw (w : ℂ) : (∫ t in 0..2*π, feature w (point t)) = ‖w‖ * 2 := by
    simp_rw [feature_eq]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right]
    have h := integral_half (0-w.arg)
    convert congrArg (fun z : ℝ => ‖w‖ * z) h using 2; ring_nf
  unfold output populationMean
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, hw, ← mul_assoc]
    rw [← Finset.sum_mul]
    field_simp
  · intro j _
    apply Continuous.intervalIntegrable
    simp_rw [feature_eq]
    exact continuous_const.mul (continuous_const.mul (continuous_half.comp (continuous_id.sub continuous_const)))

private theorem half_lipschitz (x y : ℝ) : |halfWave x-halfWave y| ≤ |x-y| :=
  (abs_max_sub_max_le_abs _ _ _).trans (abs_cos_sub_cos_le _ _)

/-- A cell centered on a grid sample. Integrating the distance to its center
costs h²/4, improving the one-sided Lipschitz quadrature constant. -/
private theorem midpoint_upper (g : ℝ → ℝ) (gc : Continuous g)
    (lip : ∀ x y, |g x - g y| ≤ |x-y|) (x h : ℝ) (hp : 0 ≤ h) :
    (∫ t in x-h/2..x+h/2, g t) ≤ h*g x+h^2/4 := by
  have left : (∫ t in x-h/2..x, g t) ≤ ∫ t in x-h/2..x, (g x + x) - t := by
    apply intervalIntegral.integral_mono_on (by linarith) (gc.intervalIntegrable _ _)
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)
    intro t ht
    have b := (le_abs_self (g t-g x)).trans (lip t x)
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at b
    change g t ≤ g x + x - t
    linarith
  have right : (∫ t in x..x+h/2, g t) ≤ ∫ t in x..x+h/2, t + (g x-x) := by
    apply intervalIntegral.integral_mono_on (by linarith) (gc.intervalIntegrable _ _)
      ((continuous_id.add continuous_const).intervalIntegrable _ _)
    intro t ht
    have b := (le_abs_self (g t-g x)).trans (lip t x)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at b
    change g t ≤ t + (g x - x)
    linarith
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => g x+x) (g := fun t : ℝ => t) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_id, smul_eq_mul] at left
  rw [intervalIntegral.integral_add (f := fun t : ℝ => t) (g := fun _ : ℝ => g x-x) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, integral_id, smul_eq_mul] at right
  rw [← intervalIntegral.integral_add_adjacent_intervals (gc.intervalIntegrable _ x)
    (gc.intervalIntegrable _ _)]
  linarith [add_le_add left right]

theorem grid_mean_lower (N : ℕ) (hN : 0 < N) (w : ℂ) :
    ((N:ℝ)/π-2)*‖w‖ ≤ ∑ i : Fin N, feature w (gridPoint N i) := by
  let h := 2*π/N
  let g := fun t : ℝ => halfWave (t-w.arg)
  let a := fun i : ℕ => h*(i:ℝ)-h/2
  have np : (0:ℝ) < N := by exact_mod_cast hN
  have hp : 0 < h := by dsimp [h]; positivity
  have hn : h*N=2*π := by dsimp [h]; field_simp
  have gc : Continuous g := continuous_half.comp (continuous_id.sub continuous_const)
  have gl : ∀ x y, |g x-g y| ≤ |x-y| := by
    intro x y
    simpa [g, sub_sub_sub_cancel_right] using half_lipschitz (x-w.arg) (y-w.arg)
  have cell (i : ℕ) : (∫ t in a i..a (i+1), g t) ≤ h*g (h*i)+h^2/4 := by
    convert midpoint_upper g gc gl (h*i) h hp.le using 2; dsimp [a]; push_cast; ring
  have b := Finset.sum_le_sum (s := Finset.range N) (fun i _ => cell i)
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => gc.intervalIntegrable (a i) (a (i+1))),
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at b
  have integral : (∫ t in a 0..a N, g t) = 2 := by
    dsimp only [g]
    rw [intervalIntegral.integral_comp_sub_right]
    convert integral_half (a 0-w.arg) using 2; dsimp [a]; rw [hn]; ring
  rw [integral] at b
  have rs : (N:ℝ)/π - 2 ≤ ∑ i ∈ Finset.range N, g (h*i) := by
    apply le_of_mul_le_mul_left (a := h) _ hp
    have eq : h*((N:ℝ)/π) = 2 := by dsimp [h]; field_simp
    have hb : (N:ℝ)*(h^2/4) ≤ 2*h := by
      calc
        _ = (h*N)*h/4 := by ring
        _ = 2*π*h/4 := by rw [hn]
        _ ≤ 2*h := by nlinarith [mul_nonneg (show 0 ≤ 4-π by linarith [pi_lt_four]) hp.le]
    linarith [show h*((N:ℝ)/π-2) = 2-2*h by rw [mul_sub,eq]; ring]
  change _ ≤ ∑ i : Fin N, feature w (point (h*(i:ℕ)))
  simp_rw [feature_eq]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => halfWave (h*(i:ℝ)-w.arg)) N]
  simpa [g, mul_comm] using mul_le_mul_of_nonneg_right rs (norm_nonneg w)


private theorem shift_sum (p : ℕ → ℝ) (N : ℕ) (period : ∀ i, p (i+N)=p i) (j : ℕ) :
    ∑ i ∈ Finset.range N, p (j+i) = ∑ i ∈ Finset.range N, p i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have a := Finset.sum_range_succ' (fun i => p (j+i)) N
    have b := Finset.sum_range_succ (fun i => p (j+i)) N
    simp only [Nat.add_zero, period] at a b
    have eqs : (∑ i ∈ Finset.range N, p (j+1+i)) =
        ∑ i ∈ Finset.range N, p (j+(i+1)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1; omega
    rw [eqs]
    linarith

private theorem cos_sq_lip (x y : ℝ) : |cos x^2-cos y^2| ≤ 2*|x-y| := by
  rw [show cos x^2-cos y^2 = (cos x-cos y)*(cos x+cos y) by ring, abs_mul]
  have hn : |cos x + cos y| ≤ 2 := (abs_add_le _ _).trans
    (by linarith [abs_cos_le_one x, abs_cos_le_one y])
  simpa [mul_comm] using mul_le_mul (abs_cos_sub_cos_le x y) hn (abs_nonneg _) (abs_nonneg _)

private theorem point_period (t : ℝ) : point (t+2*π)=point t := by
  simp [point, cos_add_two_pi,sin_add_two_pi]

/-- Put the active nodes first in cyclic order. The first (N+1)/2 nodes
contain the entire active semicircle. Each paired projection in the second
half lies within half a mesh step of the first after an antipodal rotation. -/
theorem grid_gated_sq_upper (N : ℕ) (hN : 3 ≤ N) (odd : Odd N) (u v : ℂ) :
    (∑ i : Fin N, gate u (gridPoint N i) * (inner ℝ v (gridPoint N i))^2)
      ≤ ((N:ℝ)/4+4)*‖v‖^2 := by
  obtain ⟨k,hk⟩ := odd
  have np : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have nk : (N:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast hk
  let h := 2*π/N
  have hp : 0 < h := by dsimp [h]; positivity
  have hn : h*N=2*π := by dsimp [h]; field_simp
  have kh : h*(k+1:ℝ) = π+h/2 := by rw [nk] at hn; linarith
  let b := u.arg+2*π-π/2
  let j : ℕ := ⌈b/h⌉₊
  have bp : 0 ≤ b := by dsimp [b]; linarith [Complex.neg_pi_lt_arg u, pi_pos]
  have jl : b ≤ h*j := by
    simpa [j,mul_comm] using (div_le_iff₀ hp).mp (Nat.le_ceil (b/h))
  have ju : h*j < b+h := by
    have w := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg bp hp.le)) hp
    dsimp [j]
    rw [add_mul,div_mul_cancel₀ _ hp.ne'] at w
    linarith
  let t := fun i : ℕ => h*(j+i:ℕ)
  let q := fun i : ℕ => (inner ℝ v (point (t i)))^2
  let g := fun i : ℕ => gate u (point (t i)) * q i
  have mesh (i : ℕ) : point (h*(i+N:ℕ))=point (h*i) := by
    push_cast
    rw [mul_add,hn,point_period]
  have rot (f : ℂ → ℝ) :
      (∑ i ∈ Finset.range N, f (point (t i))) = ∑ i : Fin N, f (gridPoint N i) := by
    change _ = ∑ i : Fin N, f (point (h*(i:ℕ)))
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (point (h*i))) N]
    exact shift_sum (fun i : ℕ => f (point (h*i))) N (fun i => congrArg f (mesh i)) j
  have qs : (∑ i ∈ Finset.range N, q i) = N*‖v‖^2/2 :=
    (rot (fun z => (inner ℝ v z)^2)).trans (CircleGridMoments.projection_sq_sum N hN v)
  have pq (i : ℕ) : q i = ‖v‖^2*cos (t i-v.arg)^2 := by simp only [q,projection,mul_pow]
  have qbound (i : ℕ) : q i ≤ ‖v‖^2 := by
    rw [pq]
    have sqb : cos (t i-v.arg)^2 ≤ 1 := by linarith [sin_sq_add_cos_sq (t i-v.arg), sq_nonneg (sin (t i-v.arg))]
    simpa using mul_le_mul_of_nonneg_left sqb (sq_nonneg ‖v‖)
  have gle (i : ℕ) : g i ≤ q i := by
    dsimp [g,gate]
    split_ifs <;> simp [q, sq_nonneg]
  have off (i : ℕ) (klt : k < i) (ilt : i < N) : g i = 0 := by
    have il : (k:ℝ)+1 ≤ i := by exact_mod_cast klt
    have iu : (i:ℝ)+1 ≤ N := by exact_mod_cast ilt
    have gl := mul_le_mul_of_nonneg_left il hp.le
    have gu := mul_le_mul_of_nonneg_left iu hp.le
    have cosle : cos (t i-u.arg) ≤ 0 := by
      rw [← cos_sub_two_pi (t i-u.arg)]
      apply cos_nonpos_of_pi_div_two_le_of_le <;> dsimp [t] <;> push_cast <;>
        dsimp [b] at jl ju <;> linarith
    have ug : inner ℝ u (point (t i)) ≤ 0 := by
      rw [projection]; exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) cosle
    simp only [g,gate,ite_eq_right (not_lt.mpr ug),zero_mul]
  have paired (i : ℕ) : q i ≤ q (k+1+i)+h*‖v‖^2 := by
    let a := t i-v.arg
    have phase : t (k+1+i)-v.arg = (a+h/2)+π := by
      dsimp [a,t]; push_cast; linarith
    have lip := cos_sq_lip a (a+h/2)
    rw [show a-(a+h/2) = -(h/2) by ring, abs_neg, abs_of_nonneg (by positivity : 0≤h/2)] at lip
    have dif := (le_abs_self _).trans lip
    rw [pq, pq,phase,cos_add_pi,neg_sq]
    change ‖v‖^2*cos a^2 ≤ _
    nlinarith [mul_nonneg (sq_nonneg ‖v‖) (show 0 ≤ h-(cos a^2-cos (a+h/2)^2) by linarith)]
  have split_sum (f : ℕ → ℝ) : (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ Finset.range k, f i)+f k + ∑ i ∈ Finset.range k, f (k+1+i) := by
    conv_lhs => rw [show N = (k+1)+k by omega, Finset.sum_range_add, Finset.sum_range_succ]
  have outside : (∑ i ∈ Finset.range k, g (k+1+i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact off _ (by omega) (by have := Finset.mem_range.mp hi; omega)
  have gram := rot (fun z => gate u z * (inner ℝ v z)^2)
  change (∑ i ∈ Finset.range N, g i) = _ at gram
  rw [← gram,split_sum g,outside,add_zero]
  have comp := Finset.sum_le_sum (s := Finset.range k) (fun i _ => paired i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at comp
  have raw := Finset.sum_le_sum (s := Finset.range k) (fun i _ => gle i)
  rw [split_sum q] at qs
  have khpi : (k:ℝ)*h ≤ π := by linarith
  have kh4 := mul_le_mul_of_nonneg_right (khpi.trans pi_lt_four.le) (sq_nonneg ‖v‖)
  nlinarith [gle k,qbound k,sq_nonneg ‖v‖]
end CircleAngularGeometry
