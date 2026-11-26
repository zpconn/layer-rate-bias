module

public import CircleDiscreteBudget
public import CircleReciprocalSpectral
import all CircleDiscreteBudget
import all CircleSpectralPathLength
import all CircleReciprocalSpectral
import all CircleKernelGD
import all CircleGridSpectrum
import all CircleTangentDrift
import Mathlib.Tactic

/-! Integrated residual path length for any positive fixed step at most one
and any finite grouping of the actual discrete Fourier modes. -/
@[expose] public section
noncomputable section
namespace CircleGroupedBudget
open Real Finset CircleSpectralPathLength CircleKernelGD CircleGridSpectrum CircleTangentDrift
  CircleReciprocalSpectral CircleDiscreteBudget
variable {N : ℕ} [NeZero N]

private def coeff (η : ℝ) (v : Fin N→ℝ) (t : ℕ) (r : ZMod N) : ℂ :=
  (((1-η*eigen 1 r)^t):ℝ)*normalizedCoeff v r
private def path (η : ℝ) (v : Fin N→ℝ) (t : ℕ) :=
  rmsCoordinates (fun i => (synth (coeff η v t) (ZMod.finEquiv N i)).re)

private theorem iterate (η : ℝ) (v : Fin N→ℝ) (t : ℕ) :
    ((propagator N η)^t) (rmsCoordinates v)=path η v t := by
  induction t with
  | zero =>
    have h := referencePath_zero 1 v
    have zero : coeff η v 0=normalizedCoeff v := by funext r;simp [coeff]
    simpa only [zero,pow_zero,Complex.ofReal_one,one_mul,one_apply_eq_self,path,coeff,referencePath,mul_zero,exp_zero] using h.symm
  | succ t ih =>
    rw [pow_succ',mul_apply_eq_comp,ih]
    let a := coeff η v t
    have h (i : Fin N) := matrix_synth 1 (by norm_num) (by norm_num) a i
    ext i
    change (synth a (ZMod.finEquiv N i)).re/sqrt N - η*(gramOp (sampledMatrix 1) (path η v t) i) = _
    rw [gramOp_apply]
    change _-η*((∑ j : Fin N, sampledMatrix 1 i j*((synth a (ZMod.finEquiv N j)).re/sqrt N))/N) =
      (synth (coeff η v (t+1)) (ZMod.finEquiv N i)).re/sqrt N
    simp_rw [← mul_div_assoc,←Finset.sum_div]
    rw [show η*((∑ j : Fin N, sampledMatrix 1 i j*(synth a (ZMod.finEquiv N j)).re)/sqrt N)/(N:ℝ)=
      (η*((∑ j : Fin N, sampledMatrix 1 i j*(synth a (ZMod.finEquiv N j)).re)/N))/sqrt N by ring,h,←sub_div]
    congr 1
    rw [show η*(synth (fun r => (eigen 1 r:ℂ)*a r) (ZMod.finEquiv N i)).re =
      ((η:ℂ)*synth (fun r => (eigen 1 r:ℂ)*a r) (ZMod.finEquiv N i)).re by simp,←Complex.sub_re]
    congr 1
    simp only [synth,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    dsimp only [a,coeff]
    push_cast
    rw [pow_succ']
    ring

private theorem bessel (η : ℝ) (v : Fin N→ℝ) (t : ℕ) :
    ‖path η v t‖≤blockNorm univ (coeff η v t) := by
  let a := coeff η v t
  change ‖rmsCoordinates (fun i => (synth a (ZMod.finEquiv N i)).re)‖≤blockNorm univ a
  apply (sq_le_sq₀ (norm_nonneg _) (show 0≤blockNorm univ _ from sqrt_nonneg _)).mp
  rw [rmsCoordinates_norm_sq,block_sq,div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos N)),mul_comm,←synth_parseval,←CircleGridSpectrum.fin_sum]
  exact sum_le_sum (fun i _ => sq_le_sq.mpr (by simpa using (Complex.abs_re_le_norm (synth a (ZMod.finEquiv N i)))))

private theorem grouped_decay {η : ℝ} (he : 0≤η) (hu : η≤1) (v : Fin N→ℝ) (t J : ℕ)
    (level : ZMod N→ℕ) (rate : ℕ→ℝ) (cover : ∀ r, level r≤J)
    (upper : ∀ d, rate d≤1) (floor : ∀ r, rate (level r)≤eigen 1 r) :
    ‖((propagator N η)^t) (rmsCoordinates v)‖ ≤ ∑ d ∈ range (J+1),
      (1-η*rate d)^t*blockNorm (bandSet level d) (normalizedCoeff v) := by
  rw [iterate]
  apply (bessel η v t).trans
  let a := normalizedCoeff v
  have rd (d : ℕ) : 0≤1-η*rate d := sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (upper d) he).trans (by simpa using hu))
  have hmap : ∀ r ∈ (univ:Finset (ZMod N)), level r ∈ range (J+1) := fun r _ => mem_range.mpr (Nat.lt_succ_of_le (cover r))
  have hd (d : ℕ) : ∑ r ∈ bandSet level d, ‖coeff η v t r‖^2 ≤
      ((1-η*rate d)^t*blockNorm (bandSet level d) a)^2 := by
    rw [mul_pow,block_sq,Finset.mul_sum]
    apply sum_le_sum;intro r hr
    have hrd := (mem_filter.mp hr).2
    have low := floor r
    rw [hrd] at low
    have ep : 0≤1-η*eigen 1 r := sub_nonneg.mpr ((mul_le_mul_of_nonneg_left (eigen_le_one r) he).trans (by simpa using hu))
    have ef := pow_le_pow_left₀ ep (sub_le_sub_left (mul_le_mul_of_nonneg_left low he) 1) t
    rw [coeff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ep t),mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg ep _) ef 2) (sq_nonneg _)
  have non (d : ℕ) : 0≤(1-η*rate d)^t*blockNorm (bandSet level d) a := mul_nonneg (pow_nonneg (rd d) _) (sqrt_nonneg _)
  apply (sq_le_sq₀ (show 0≤blockNorm univ _ from sqrt_nonneg _) (sum_nonneg (fun d _ => non d))).mp
  rw [block_sq,←sum_fiberwise_of_maps_to hmap]
  exact (sum_le_sum (fun d _ => hd d)).trans (sum_sq_le_sq_sum_of_nonneg fun d _ => non d)

private theorem geom {η d : ℝ} (he : 0<η) (hu : η≤1) (hd : 0<d) (du : d≤1) (T : ℕ) :
    η*(∑ t ∈ range T, (1-η*d)^t)≤d⁻¹ := by
  have p : 0≤1-η*d := sub_nonneg.mpr ((mul_le_mul_of_nonneg_left du he.le).trans (by simpa using hu))
  have balance (j : ℕ) : η*(∑ t ∈ range j, (1-η*d)^t)*d+(1-η*d)^j=1 := by
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ,pow_succ];linarith only [ih]
  rw [←one_div,le_div_iff₀ hd]
  linarith only [balance T,pow_nonneg p T]

/-- The sum through any finite prefix is bounded by the same grouped budget,
uniformly over the fixed positive learning rate. -/
theorem grouped_area {η : ℝ} (he : 0<η) (hu : η≤1) (v : Fin N→ℝ) (T J : ℕ)
    (level : ZMod N→ℕ) (rate : ℕ→ℝ) (cover : ∀ r, level r≤J)
    (pos : ∀ d, 0<rate d) (upper : ∀ d, rate d≤1) (floor : ∀ r, rate (level r)≤eigen 1 r) :
    η*(∑ t ∈ range T, ‖((propagator N η)^t) (rmsCoordinates v)‖)≤
    pathBudget J level rate (normalizedCoeff v) := by
  apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun t _ => grouped_decay he.le hu v t J level rate cover upper floor)) he.le).trans
  rw [sum_comm,Finset.mul_sum]
  unfold pathBudget
  apply sum_le_sum;intro d _
  rw [←Finset.sum_mul,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (geom he hu (pos d) (upper d) T) (sqrt_nonneg _)

/-- Existing dyadic L⁴ budget controls the same variable-step physical path. -/
theorem dyadic_area {η : ℝ} (he : 0<η) (hu : η≤1) (ho : Odd N) (T m : ℕ)
    (z : CircleEscapeBridge.Seed m) :
    η*(∑ t ∈ range T, ‖((propagator N η)^t) (rmsCoordinates (rawResidual N m z))‖)≤seedBudget ho m z := by
  unfold seedBudget
  change _ ≤ pathBudget _ _ CircleDiscreteBudget.rate _
  simpa only [show normalizedCoeff (rawResidual N m z) = _ from funext (fun r => normalizedCoeff_raw m r z)] using
    grouped_area he hu (rawResidual N m z) T (N+1).log2 (shell ho) rate (shell_le ho) rate_pos rate_le_one
      (fun r => shell_eigen ho (τ:=1) (by norm_num) (by norm_num) r)
end CircleGroupedBudget
