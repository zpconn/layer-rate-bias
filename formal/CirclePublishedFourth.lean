module
public import CircleContinuationBound
import all CircleFlowMoments
import all CircleActualTracking
import all CircleEscapeBridge
import all CircleFlowPath
import all CircleInitializationConcentration
import all CircleTangentDrift
import Mathlib.Tactic

/-! Width-uniform fourth norm with the numerical constants of followup/flow.md. -/
public section
noncomputable section
namespace CirclePublishedFourth
open Real MeasureTheory ProbabilityTheory CircleFlowPath CircleFlowMoments CircleActualTracking
  CircleInitializationConcentration CircleEscapeBridge CircleTangentDrift
variable {N m : ℕ}

private theorem loss_constant : lossConstant ≤ 18 := by
  have h : outputConstant ≤ 4 := by
    unfold outputConstant
    rw [standardEighth_eq,Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num)]
    norm_num
  have q : 0≤outputConstant := by unfold outputConstant;positivity
  unfold lossConstant
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤(8+outputConstant) by positivity)]

private theorem gaussian_square : gaussianSquareNorm ≤ 4 := by
  rw [gaussianSquareNorm,lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) (by fun_prop)]
  have v (x : ℝ) : ‖x^2‖ ^ (4:ℝ) = x^8 := by
    rw [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    ring
  simp only [ENNReal.toReal_ofNat,v]
  change standardEighth ^ (4:ℝ)⁻¹ ≤ 4
  rw [standardEighth_eq,Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem pointwise {T b : ℝ} (hN : 3≤N) (hm : 0<m) (ht : 0≤T) (hb : |b|≤1)
    (z : ℝ→State m) (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T z) :
    |mean (z T)-reference N m b (z 0)| ≤
      (3+(sqrt T/(2*π*m))*squared (z 0))+
        (1/6+sqrt T/(2*π)+T/(2*π*sqrt m))*initialLoss N m (z 0) := by
  let E := squared (z 0)
  let L := initialLoss N m (z 0)
  let R := ‖gridR N (z 0)‖
  have R2 : R^2=2*L := gridR_sq _
  have l0 : 0≤L := by unfold L initialLoss loss;positivity
  have rp : 0≤R := norm_nonneg _
  have ep : 0≤E := by unfold E squared;positivity
  have sN : 0<(m:ℝ) := by exact_mod_cast hm
  have hR : R ≤ 3+L/6 := by nlinarith [sq_nonneg (R-6)]
  have op := ((rowOp (fun _ : Fin N => b)).le_opNorm (gridR N (z 0))).trans
    (mul_le_mul_of_nonneg_right (rowOp_norm (by omega : 0<N) zero_le_one (fun _ => hb)) rp)
  have er : |mean (z 0)-reference N m b (z 0)|≤R := by
    rw [←actual_reference hN (z 0) b,sub_sub_cancel,←Real.norm_eq_abs]
    simpa [R] using op
  let d := R * sqrt (T/2)
  have dv := CircleContinuationBound.continuation (by norm_num : (0:ℝ)<1) ht F
  simp only [max_self,one_mul] at dv
  change |mean (z T)-mean (z 0)|≤d*(sqrt E+d/2)/(π*sqrt m) at dv
  have dp : 0≤d := by dsimp [d];positivity
  have dd : d^2=T*L := by dsimp [d]; rw [mul_pow,R2,sq_sqrt (by positivity)];ring
  have deq : d=sqrt T*sqrt L := by
    apply (sq_eq_sq₀ dp (by positivity)).mp
    rw [dd,mul_pow,sq_sqrt ht,sq_sqrt l0]
  have ee : sqrt E/sqrt (m:ℝ)*sqrt L ≤ (E/m+L)/2 := by
    have q := sq_nonneg (sqrt E/sqrt (m:ℝ)-sqrt L)
    nlinarith [show (sqrt E/sqrt (m:ℝ))^2=E/m by rw [div_pow,sq_sqrt ep,sq_sqrt sN.le],sq_sqrt l0]
  have bnd := mul_le_mul_of_nonneg_left ee (show 0≤sqrt T/π by positivity)
  have mv : d*(sqrt E+d/2)/(π*sqrt m) ≤
      sqrt T/(2*π*m)*E+(sqrt T/(2*π)+T/(2*π*sqrt m))*L := by
    calc
      _ = (sqrt T/π)*(sqrt E/sqrt m*sqrt L)+(T*L)/(2*π*sqrt m) := by
        rw [show d*(sqrt E+d/2)=d*sqrt E+d^2/2 by ring,dd,deq];ring
      _ ≤ (sqrt T/π)*((E/m+L)/2)+(T*L)/(2*π*sqrt m) := add_le_add_left bnd _
      _ = _ := by ring
  have tri := abs_sub_le (mean (z T)) (mean (z 0)) (reference N m b (z 0))
  change _ ≤ (3+(sqrt T/(2*π*m))*E)+(1/6+sqrt T/(2*π)+T/(2*π*sqrt m))*L
  linarith [dv.trans mv,er.trans hR]

theorem fourth {T b : ℝ} (hN : 3≤N) (hm : 0<m) (ht : 0≤T) (hb : 0≤b) (h1 : b≤1)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T (z ω))
    (_meas : Measurable fun ω => z ω T) :
    lpNorm (fun ω => mean (z ω T)-reference N m b ω) 4 (seedLaw m) ≤
      6+6*sqrt (6*T)+9*T/sqrt m := by
  let μ := seedLaw m
  let a := sqrt T/(2*π*m)
  let k := 1/6+sqrt T/(2*π)+T/(2*π*sqrt m)
  let E := squared (m:=m)
  let L := initialLoss N m
  let A := fun ω => a*E ω
  let B := fun ω => k*L ω
  let K := fun ω => (3+A ω)+B ω
  have ap : 0≤a := by unfold a;positivity
  have kp : 0≤k := by unfold k;positivity
  have leL := initial_loss_fourth (by omega : 0<N) hm
  have mA : MemLp A 4 μ := squared_mem.const_mul _
  have mB : MemLp B 4 μ := leL.1.const_mul _
  have mC := (memLp_const (p:=4) (μ:=μ) (3:ℝ)).add mA
  have bound := lpNorm_mono_real (f:=fun ω => mean (z ω T)-reference N m b ω) (g:=K) (mC.add mB) (fun ω => by
    simpa only [Real.norm_eq_abs,start ω] using pointwise hN hm ht (b:=b) (by simpa only [abs_of_nonneg hb] using h1) (z ω) (flow ω))
  have he := (gaussian_energy_norm m).trans (mul_le_mul_of_nonneg_left gaussian_square (by positivity))
  have hl := leL.2.trans loss_constant
  have aN : lpNorm A 4 μ≤a*((3*(m:ℝ))*4) := by
    rw [show lpNorm A 4 μ=|a| *lpNorm E 4 μ from lp_scale a E,abs_of_nonneg ap]
    exact mul_le_mul_of_nonneg_left he ap
  have bN : lpNorm B 4 μ≤k*18 := by
    rw [show lpNorm B 4 μ=|k| *lpNorm L 4 μ from lp_scale k L,abs_of_nonneg kp]
    exact mul_le_mul_of_nonneg_left hl kp
  have t1 := lpNorm_add_le mC (g:=B) (by norm_num)
  have t2 := lpNorm_add_le (memLp_const (p:=4) (μ:=μ) (3:ℝ)) (g:=A) (by norm_num)
  change lpNorm K 4 μ ≤ _ at t1
  rw [lp_const] at t2
  have sm : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have p : 1/π ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) pi_gt_three.le
  have scalar : 3+a*((3*(m:ℝ))*4)+k*18 ≤ 6+6*sqrt (6*T)+9*T/sqrt m := by
    have one : sqrt T ≤ sqrt (6*T) := sqrt_le_sqrt (by linarith)
    have t := mul_le_mul_of_nonneg_right p (sqrt_nonneg T)
    have q := mul_le_mul_of_nonneg_right p (show 0≤T/sqrt m by positivity)
    have eq : 3+a*((3*(m:ℝ))*4)+k*18 =
        6+15*(1/π*sqrt T)+9*((1/π)*(T/sqrt m)) := by
      dsimp [a,k]
      field_simp [sm];ring
    rw [eq]
    have x := mul_le_mul_of_nonneg_left t (by norm_num : (0:ℝ)≤15)
    have y := mul_le_mul_of_nonneg_left q (by norm_num : (0:ℝ)≤9)
    have r : 0≤T/sqrt (m:ℝ) := by positivity
    rw [mul_div_assoc]
    linarith [sqrt_nonneg T]
  apply bound.trans
  apply t1.trans
  exact (add_le_add (t2.trans (add_le_add_right aN _)) bN).trans (by simpa using scalar)
/-- The single-coefficient exceptional-path envelope used at both clocks. -/
theorem twenty {T b : ℝ} (hN : 3≤N) (hm : 0<m) (ht : 0≤T) (hb : 0≤b) (h1 : b≤1)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T (z ω))
    (meas : Measurable fun ω => z ω T) :
    lpNorm (fun ω => mean (z ω T)-reference N m b ω) 4 (seedLaw m) ≤
      20*(1+sqrt T+T/sqrt m) := by
  apply (fourth hN hm ht hb h1 z start flow meas).trans
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 6),mul_div_assoc]
  have h : sqrt 6 ≤ 3 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  nlinarith [mul_le_mul_of_nonneg_right h (sqrt_nonneg T),show 0≤T/sqrt m by positivity,sqrt_nonneg T]

/-- L⁴ membership and the explicit norm bound for the same measurable endpoint. -/
theorem mem_and_bound {T b : ℝ} (hN : 3≤N) (hm : 0<m) (ht : 0≤T) (hb : 0≤b) (h1 : b≤1)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T (z ω))
    (meas : Measurable fun ω => z ω T) :
    let Y := fun ω => mean (z ω T)-reference N m b ω
    MemLp Y 4 (seedLaw m) ∧ lpNorm Y 4 (seedLaw m) ≤ 6+6*sqrt (6*T)+9*T/sqrt m :=
  ⟨(gaussian_flow_fourth_sharp (by omega) hm (by norm_num) (by norm_num)
    ht hb h1 z start flow meas).1, fourth hN hm ht hb h1 z start flow meas⟩

end CirclePublishedFourth
