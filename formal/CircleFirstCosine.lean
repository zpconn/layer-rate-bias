module

public import CircleAngularGeometry
import all CircleAngularGeometry
import all CircleEscape
import Mathlib.Tactic

/-! Exact first-cosine measurement proposed in the research plan, including
the simultaneous-update cross term. -/
public section
noncomputable section
namespace CircleFirstCosine
open Real MeasureTheory CircleEscape CircleAngularGeometry

def amplitude (f : ℂ → ℝ) := (∫ t in 0..2*π, f (point t)*cos t)/π

private theorem projection_xy (w : ℂ) (t : ℝ) :
    inner ℝ w (point t)=w.re*cos t+w.im*sin t := by
  simp [Complex.inner,Complex.mul_re,point]
  ring

private theorem one_integral (w : ℂ) :
    (∫ t in 0..2*π, feature w (point t)*cos t) = π/2*w.re := by
  let g := fun t => feature w (point t)*cos t
  have cont : Continuous g := by
    simp only [g,feature,projection_xy]
    fun_prop
  have pair (t : ℝ) : g t+g (t+π)=(w.re*cos t+w.im*sin t)*cos t := by
    simp only [g,feature,projection_xy]
    simp only [cos_add_pi,sin_add_pi]
    rw [show w.re * -cos t+w.im * -sin t= -(w.re*cos t+w.im*sin t) by ring]
    by_cases h : 0≤w.re*cos t+w.im*sin t
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)];ring
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))];ring
  change (∫ t in 0..2*π,g t)=_
  rw [← intervalIntegral.integral_add_adjacent_intervals (cont.intervalIntegrable 0 π) (cont.intervalIntegrable π (2*π))]
  have shift : (∫ t in π..2*π,g t)=(∫ t in 0..π,g (t+π)) := by
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add,two_mul]
  rw [shift,←intervalIntegral.integral_add (f:=g) (g:=fun t => g (t+π)) (cont.intervalIntegrable 0 π)
    ((cont.comp (continuous_id.add continuous_const)).intervalIntegrable 0 π)]
  simp_rw [pair]
  simp_rw [show ∀ t:ℝ,(w.re*cos t+w.im*sin t)*cos t=w.re*(cos t)^2+w.im*(sin t*cos t) by intro t;ring]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable (fun t => w.re*(cos t)^2) volume 0 π)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable (fun t => w.im*(sin t*cos t)) volume 0 π),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_cos_sq,integral_sin_mul_cos₁]
  simp;ring

/-- For arbitrary finite weights, 2Q(f cos) is one half the first Cartesian
component of the readout-weight product, at the original network scaling. -/
theorem actual_amplitude {m : ℕ} (c : ℝ) (u : Net ℂ m) :
    amplitude (output c u)=(c/2)*∑ j, u.a j*(u.w j).re := by
  unfold amplitude output
  simp_rw [mul_assoc,Finset.sum_mul]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc,intervalIntegral.integral_const_mul,one_integral,
      show ∀ i, u.a i*(π/2*(u.w i).re)=π/2*(u.a i*(u.w i).re) by intro;ring]
    rw [←Finset.mul_sum]
    field_simp
  · intro j _
    simp only [feature,projection_xy]
    apply Continuous.intervalIntegrable
    fun_prop

theorem teacher : amplitude (fun x => 1+x.re)=1 := by
  unfold amplitude
  simp only [point,add_mul,one_mul,←sq]
  rw [intervalIntegral.integral_add (f:=cos) (g:=fun t => (cos t)^2) (continuous_cos.intervalIntegrable _ _)
    ((continuous_cos.pow 2).intervalIntegrable _ _),integral_cos,integral_cos_sq]
  simp [Real.pi_ne_zero]

/-- Simultaneous readout and hidden updates, for arbitrary increments. -/
theorem simultaneous_change {m : ℕ} (c : ℝ) (u v : Net ℂ m) :
    amplitude (output c v)-amplitude (output c u) = (c/2)*∑ j,
      ((v.a j-u.a j)*(u.w j).re + u.a j*((v.w j).re-(u.w j).re) +
       (v.a j-u.a j)*((v.w j).re-(u.w j).re)) := by
  rw [actual_amplitude,actual_amplitude,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end CircleFirstCosine
