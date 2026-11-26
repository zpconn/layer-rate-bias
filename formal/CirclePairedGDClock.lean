module

public import CircleFlowTracking
public import CircleFiniteConfidence
import all CircleKernelGD
import Mathlib.Tactic

/-! Deterministic radius and residual estimates for unit-step training at the
same integer horizon as the paired flow. The 32nd root records the fractional
powers in the terminal residual without rounding its exponent. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDClock
open Real

def rate (x : ℝ) := 15/(32*(π*x)^2)

theorem absorb {x : ℝ} (hx : 1000000 ≤ x) {a b : ℕ} (h : a+1 ≤ b) :
    1000000*x^a ≤ x^b := by
  have h1 : 1≤x := by linarith
  calc
    _ ≤ x*x^a := mul_le_mul_of_nonneg_right hx (pow_nonneg (by linarith) _)
    _ = x^(a+1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ h1 h

theorem rate_bounds {x : ℝ} (hx : 1≤x) :
    0<rate x ∧ rate x≤1 ∧ 1 ≤ rate x*(40*x^2) := by
  have xp : 0<x := by linarith
  have pi2 : 1 ≤ π^2 := by nlinarith [pi_gt_three]
  have x2 : 1≤x^2 := one_le_pow₀ hx
  have rat : π^2<16 := by nlinarith [pi_lt_four, pi_pos]
  unfold rate
  refine ⟨by positivity, (div_le_iff₀ (by positivity)).2 ?_,?_⟩
  · nlinarith only [mul_le_mul pi2 x2 zero_le_one (sq_nonneg _)]
  · field_simp
    nlinarith only [mul_lt_mul_of_pos_right rat (sq_pos_of_pos xp)]

theorem root_pow {x : ℝ} (hx : 0<x) (j : ℕ) :
    (x^(1/32:ℝ))^j = x^((j:ℝ)/32) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  congr 1; ring

theorem root_spec {x : ℝ} (hx : 4^32≤x) :
    let w := x^(1/32:ℝ)
    4≤w ∧ w^32=x := by
  have xp : 0<x := by norm_num at hx; linarith
  intro w
  have eq : w^32=x := by dsimp [w];rw [root_pow xp 32]; norm_num
  refine ⟨le_of_pow_le_pow_left₀ (n:=32) (by decide) (rpow_nonneg xp.le _) ?_,eq⟩
  rwa [eq]

theorem residual_clock {x w : ℝ} (hw : 4≤w) (hroot : w^32=x) :
    (1-rate x)^(CircleFlowTracking.horizon x)*sqrt (12/(1/sqrt x)) ≤ 4/w^97 := by
  have wp : 0<w := by linarith
  have x1 : 1≤x := hroot ▸ one_le_pow₀ (by linarith)
  have xp : 0<x := by linarith
  obtain ⟨kp,k1,_⟩ := rate_bounds x1
  have root : sqrt x=w^16 := by rw [←hroot,show w^32=(w^16)^2 by ring,sqrt_sq (by positivity)]
  have Ra : sqrt (12/(1/sqrt x))≤4*w^8 := by
    rw [root]
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    field_simp
    nlinarith only [pow_nonneg wp.le 16]
  have lb : w^112 ≤ 2*sqrt (12*x)*x^3 := by
    have h : w^16 ≤ sqrt (12*x) := by
      rw [←root];exact sqrt_le_sqrt (by linarith)
    calc
      _ = w^16*x^3 := by rw [←hroot];ring
      _ ≤ (2*sqrt (12*x))*x^3 := by gcongr; linarith [sqrt_nonneg (12*x)]
  have logb := Real.log_le_log (by positivity : 0<w^112) lb
  rw [Real.log_pow] at logb
  change 112*log w ≤ log (2*sqrt (12*x)*x^3) at logb
  have clk := Nat.le_ceil (2*π^2*x^2*log (2*sqrt (12*x)*x^3))
  have km : rate x*(2*π^2*x^2) = 15/16 := by unfold rate;field_simp;ring
  have clk' : 105*log w ≤ rate x*(CircleFlowTracking.horizon x:ℝ) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left clk kp.le)
    rw [← mul_assoc,km]
    linarith only [logb]
  have est := Real.exp_le_exp.mpr (neg_le_neg clk')
  rw [show -(105*log w)= -log (w^105) by rw [log_pow];norm_num,Real.exp_neg (log (w^105)),Real.exp_log (by positivity)] at est
  calc
    _ ≤ Real.exp (-(rate x*(CircleFlowTracking.horizon x:ℝ))) * sqrt (12/(1/sqrt x)) := by
      apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
      convert CircleKernelGD.disc_exp k1 (CircleFlowTracking.horizon x) using 1
    _ ≤ (w^105)⁻¹*(4*w^8) := mul_le_mul est Ra (sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp

end CirclePairedGDClock
