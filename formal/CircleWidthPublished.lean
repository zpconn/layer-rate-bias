module

public import CircleWidthFinite
public import CircleWidthInitTail
public import CircleWidthResidualTail
import all CircleWidthFinite
import all CircleWidthTracking
import all CircleWidthMoment
import all CircleGaussianTracking
import all CircleInitializationConcentration
import all CircleTangentDrift
import all CircleEscapeBridge
import all CircleActualTracking
import Mathlib.Tactic

/-! Finite nonasymptotic confidence and root-MSE for unrestricted GD. -/
@[expose] public section
noncomputable section
namespace CircleWidthPublished
open Real MeasureTheory Set CircleWidthTracking CircleWidthMoment CircleGaussianTracking
  CircleEscapeBridge CircleTangentDrift CircleGridSpectrum CircleWidthFinite

def cutoff (m T : ℕ) : ℝ := m/(1200^2*(1+(T:ℝ))^4)
def coefficient (m T : ℕ) : ℝ := 27000*(1+(T:ℝ))^2/sqrt m

private theorem tail_from_residual {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η : ℝ} (hη : 0≤η) (hc : η≤1) {d : ℝ} (d1 : 1≤d) (dc : d≤cutoff m T)
    (initial_tail : (seedLaw m).real {z | 2+sqrt (8*d) < initialRms (n+1) m z} ≤ 2*(n+1:ℝ)*exp (-d)) :
    (seedLaw m).real {z | coefficient m T*d< |rawError (n+1) m T η (stoppedCoefficient n T η) z|} ≤
      exp (logCount (n+1)-d) := by
  let w : ℝ := 1+T
  let q := sqrt d/sqrt m
  let u := 64*q
  let ρ := 10*T*q
  let R := 2+sqrt (8*d)
  let e := 2*(30*ρ+3*u)
  have wp : 0<w := by dsimp [w];positivity
  have w1 : 1≤w := by dsimp [w];linarith [Nat.cast_nonneg (α:=ℝ) T]
  have tw : (T:ℝ)≤w := by dsimp [w];linarith
  have mp : 0<sqrt (m:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have d0 : 0≤d := by linarith
  have su : 1≤sqrt d := one_le_sqrt.mpr d1
  have qp : 0≤q := div_nonneg (sqrt_nonneg d) mp.le
  have qq : q*(1200*w^2)≤1 := by
    have di : d*(1200^2*w^4)≤m := (le_div_iff₀ (by positivity)).mp dc
    have rt := sqrt_le_sqrt di
    have eq : sqrt (d*(1200^2*w^4))=sqrt d*(1200*w^2) := by
      rw [sqrt_mul d0,show (1200:ℝ)^2*w^4=(1200*w^2)^2 by ring,sqrt_sq (by positivity)]
    rw [eq] at rt
    dsimp [q];rw [div_mul_eq_mul_div,div_le_one mp];exact rt
  have wu : 0≤u := by dsimp [u];positivity
  have r0 : 0≤ρ := by dsimp [ρ];positivity
  have two : 1≤w^2 := one_le_pow₀ w1
  have q1 : 1200*q≤1 := by nlinarith only [qq,mul_le_mul_of_nonneg_left two qp]
  have t2 : (T:ℝ)≤w^2 := tw.trans ((by simpa using (pow_le_pow_right₀ w1 (by decide : 1≤2))))
  have r1 : ρ≤1/120 := by dsimp [ρ];nlinarith only [qq,mul_le_mul_of_nonneg_right t2 qp]
  have u1 : u≤1 := by dsimp [u];linarith
  have rle : R≤(49/10)*sqrt d := by
    dsimp [R];rw [sqrt_mul (by norm_num)]
    have sr : sqrt (8:ℝ)≤29/10 := (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
    nlinarith only [su,mul_le_mul_of_nonneg_right sr (sqrt_nonneg d)]
  have ee : e≤600*w*q := by dsimp [e,ρ,u,w];nlinarith only [qp]
  have ww : (T:ℝ)*w≤w^2 := by nlinarith only [mul_le_mul_of_nonneg_right tw wp.le]
  have budget : (T:ℝ)*e≤1/2 := by
    nlinarith only [qq,mul_le_mul_of_nonneg_left ee (Nat.cast_nonneg T),mul_le_mul_of_nonneg_right ww qp]
  have drift : (T:ℝ)*(2*(1+ρ)/sqrt m*R)≤ρ := by
    have prod := mul_le_mul (show 2*(1+ρ) ≤ 121/60 by linarith) rle (by dsimp [R];positivity) (by norm_num)
    have less : 2*(1+ρ)*R≤10*sqrt d := by nlinarith only [prod,sqrt_nonneg d]
    have le := div_le_div_of_nonneg_right less mp.le
    simpa only [ρ,q,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left le (Nat.cast_nonneg T)
  have err : 6*e*R*T≤coefficient m T*d := by
    have p := mul_le_mul ee rle (by dsimp [R];positivity) (by positivity)
    have qd : q*sqrt d=d/sqrt m := by dsimp [q];rw [div_mul_eq_mul_div,←sq,sq_sqrt d0]
    have compat : 600*w*q*(49/10*sqrt d)=2940*w*(d/sqrt m) := by rw [←qd];ring
    rw [compat] at p
    have W := mul_le_mul_of_nonneg_right ww (div_nonneg d0 mp.le)
    change _≤27000*w^2/sqrt m*d
    nlinarith only [mul_le_mul_of_nonneg_right p (Nat.cast_nonneg T),W,mul_nonneg (sq_nonneg w) (div_nonneg d0 mp.le),
      show 27000*w^2/sqrt m*d=27000*(w^2*(d/sqrt m)) by ring]
  let F : Set (Seed m) := {z | ¬GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => CircleSpectrum.k0 1) z}
  let E := {z | R < initialRms (n+1) m z}
  have sub : {z | coefficient m T*d< |rawError (n+1) m T η (stoppedCoefficient n T η) z|} ⊆ F∪E := by
    intro z hz
    by_contra bad
    have g : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => CircleSpectrum.k0 1) z := by
      by_contra fg;exact bad (Or.inl fg)
    have r : initialRms (n+1) m z≤R := le_of_not_gt (fun eg => bad (Or.inr eg))
    exact (not_lt.mpr ((stopped_tracking_neuron n m T hn odd hm z hη hc g r0 (by linarith) wu r drift budget).trans err)) hz
  have eq : -(m:ℝ)*u^2/4096= -d := by
    dsimp [u,q];rw [mul_pow,div_pow,sq_sqrt d0,sq_sqrt (Nat.cast_nonneg m)];field_simp;ring
  have g := CircleWidthInitTail.good_init (N:=n+1) hm r0 (by linarith) wu u1
  rw [eq] at g
  apply (measureReal_mono sub).trans ((measureReal_union_le (μ:=seedLaw m) F E).trans ((add_le_add g initial_tail).trans ?_))
  rw [logCount,sub_eq_add_neg,exp_add,exp_log (by positivity)]
  push_cast
  nlinarith only [mul_nonneg (exp_nonneg (-d)) (sq_nonneg (n:ℝ)),
    mul_nonneg (exp_nonneg (-d)) (Nat.cast_nonneg (α:=ℝ) n),exp_nonneg (-d)]

/-- Published initialization confidence at every admissible real tail parameter.
The bound includes all tangent entries, the angular row, the total energy, the
weighted margin counts, their angular mean, and the initial grid residual. -/
theorem initialization_confidence {N m : ℕ} [NeZero N] (hm : 0<m) {d ρ : ℝ}
    (hd : 0≤d) (dm : d≤m) (r0 : 0≤ρ) (r1 : ρ≤1) (u1 : 64*sqrt (d/m)≤1) :
    (seedLaw m).real ({z | ¬GoodInit 1 ρ (64*sqrt (d/m)) (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) z} ∪
      {z | 2+sqrt (8*d) < initialRms N m z}) ≤ 8*((N:ℝ)+1)^2*exp (-d) := by
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have a := CircleWidthInitTail.good_init (N:=N) hm r0 r1 (by positivity) u1
  have eq : -(m:ℝ)*(64*sqrt (d/m))^2/4096= -d := by
    rw [mul_pow,sq_sqrt (by positivity)];field_simp;ring
  rw [eq] at a
  have b := CircleWidthResidualTail.initial_residual (N:=N) (Nat.pos_of_ne_zero (NeZero.ne N)) hm hd dm
  apply (measureReal_union_le (μ:=seedLaw m) _ _).trans ((add_le_add a b).trans ?_)
  nlinarith only [mul_nonneg (exp_nonneg (-d)) (sq_nonneg (N:ℝ)),mul_nonneg (exp_nonneg (-d)) (Nat.cast_nonneg (α:=ℝ) N),exp_nonneg (-d)]

theorem actual_tail {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η : ℝ} (hη : 0≤η) (hc : η≤1) {d : ℝ} (d1 : 1≤d) (dc : d≤cutoff m T) :
    (seedLaw m).real {z | coefficient m T*d< |rawError (n+1) m T η (stoppedCoefficient n T η) z|} ≤
      exp (logCount (n+1)-d) := by
  have small : cutoff m T≤m := by
    apply div_le_self (Nat.cast_nonneg _) _
    have h : (1:ℝ)≤(1+(T:ℝ))^4 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) T])
    linarith
  apply tail_from_residual hn odd hm hη hc d1 dc
  simpa only [Nat.cast_add,Nat.cast_one] using CircleWidthResidualTail.initial_residual (N:=n+1) (by omega) hm
    (by linarith : 0≤d) (dc.trans small)

/-- Formula (1) of width-upper.md with its numerical constants and original seed law. -/
theorem finite {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    (width : 4*3^T≤m) (level_ge : 1≤cutoff m T) {η : ℝ} (hη : 0≤η) (hc : η≤1) :
    let B := 8*(((n+1:ℕ):ℝ)+1)^2
    let h := log B
    sqrt (∫ z, (rawError (n+1) m T η (stoppedCoefficient n T η) z)^2 ∂seedLaw m) ≤
      coefficient m T*sqrt (h^2+2*h+2)+2*sqrt m*14^(3^T)*(min 1 (B*exp (-cutoff m T)))^(1/4:ℝ) := by
  intro B h
  have b := CircleWidthFinite.stopped_bounds n T hη hc
  have p := finite_rms (CircleWidthFinite.error_meas ..) (raw_mem4 ..) (by unfold coefficient;positivity)
    level_ge (CircleWidthFinite.logCount_ge_one (n+1)) (by positivity)
    (fun _ lo hi => actual_tail hn odd hm hη hc lo hi) (actual_fourth (by omega) hm width hη hc b.1 b.2)
  have eq : exp (logCount (n+1)-cutoff m T)=B*exp (-cutoff m T) := by
    rw [logCount,sub_eq_add_neg,exp_add,exp_log (by positivity)]
  rw [eq] at p
  have nn : 0≤min 1 (B*exp (-cutoff m T)) := le_min zero_le_one (by dsimp [B];positivity)
  have roots (x : ℝ) (hx : 0≤x) : sqrt (sqrt x)=x^(1/4:ℝ) := by
    rw [sqrt_eq_rpow,sqrt_eq_rpow,←rpow_mul hx];norm_num
  rw [roots _ nn] at p
  exact p
end CircleWidthPublished
