module

public import CircleKernelGD
public import CircleTruncatedBudget
import all CircleTruncatedBudget
public import CircleSpectralPathLength
import all CircleKernelGD
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleSpectralPathLength
import all CircleTangentDrift
import Mathlib.Tactic

/-! Integrated discrete residual path length from the true per-frequency
equal-rate Euler multipliers, retaining the finite stopping horizon. -/
public section
noncomputable section
namespace CircleDiscreteBudget
open CircleKernelGD CircleSpectralPathLength CircleGridSpectrum CircleKernelIdentification CircleSpectrum
  CircleTangentDrift CircleEscapeBridge CircleResidualSpectrum Real Finset
variable {N : ℕ} [NeZero N]

/-- Every discrete eigenvalue is at most the diagonal value of the unsampled
kernel, obtained by summing all its nonnegative continuum coefficients. -/
theorem eigen_le_one (r : ZMod N) : eigen 1 r ≤ 1 := by
  let a := tangentCoeff 1
  have ha := tangentCoeff_summable 1 (by norm_num) (by norm_num)
  have sum : ∑' k, a k=1 := by
    have h := sampled_tangent_eq_series (N:=N) 1 (by norm_num) (by norm_num) 0
    have hp : gridAngle (0:ZMod N)=((0:ℝ):AddCircle (π- -π)) := by simp [gridAngle]
    have hf : (periodicTangent 1 ((0:ℝ):AddCircle (π- -π))).re=1 := by
      have h0 := periodicTangent_cartesian 1 0 0
      simp only [sub_zero,cartesian_kernel_isotropic,abs_zero,angular_tangent 1 0 (by norm_num) pi_pos.le,sin_zero,cos_zero] at h0
      convert h0 using 1
      field_simp;ring
    have hz := congrArg Complex.re h
    simp only [hp,series,char,mul_zero,AddChar.map_zero_eq_one,mul_one,←Complex.ofReal_tsum,Complex.ofReal_re,hf] at hz
    exact hz.symm
  let f (k : ℤ) := if (k:ZMod N)=r then a k else 0
  have hb (k : ℤ) : f k≤a k := by dsimp [f];split <;> first | rfl | exact tangentCoeff_nonneg (by norm_num) _
  have hf : Summable f := ((tangentCoeff_summable 1 (by norm_num) (by norm_num)).indicator {k : ℤ | (k:ZMod N)=r}).congr (fun k => by simp [Set.indicator_apply,f,a])
  exact (hf.tsum_le_tsum hb ha).trans_eq sum

private def path (v : Fin N→ℝ) (t : ℕ) := rmsCoordinates (fun i =>
  (synth (fun r => ((1-eigen 1 r)^t:ℝ)*normalizedCoeff v r) (ZMod.finEquiv N i)).re)

private theorem iter_eq (v : Fin N→ℝ) (t : ℕ) : ((update N)^t) (rmsCoordinates v)=path v t := by
  induction t with
  | zero =>
    have h := referencePath_zero 1 v
    simpa only [pow_zero,Complex.ofReal_one,one_mul,one_apply_eq_self,path,referencePath,mul_zero,exp_zero] using h.symm
  | succ t ih =>
    rw [pow_succ',mul_apply_eq_comp,ih]
    let a (r : ZMod N) := (↑((1-eigen 1 r)^t):ℂ)*normalizedCoeff v r
    have h (i : Fin N) := matrix_synth 1 (by norm_num) (by norm_num) a i
    ext i
    change (synth a (ZMod.finEquiv N i)).re/sqrt N - gramOp (sampledMatrix 1) (path v t) i = _
    rw [gramOp_apply]
    change _-(∑ j : Fin N, sampledMatrix 1 i j*((synth a (ZMod.finEquiv N j)).re/sqrt N))/N =
      (synth (fun r => ((1-eigen 1 r)^(t+1):ℝ)*normalizedCoeff v r) (ZMod.finEquiv N i)).re/sqrt N
    simp_rw [← mul_div_assoc,←Finset.sum_div]
    rw [div_right_comm _ (sqrt _) (N:ℝ),h,←sub_div]
    congr 1
    rw [←Complex.sub_re]
    congr 1
    simp only [synth,←Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro r _
    dsimp [a]
    push_cast
    rw [pow_succ']
    ring

private theorem path_norm (v : Fin N→ℝ) (t : ℕ) :
    ‖path v t‖≤blockNorm univ (fun r => ((1-eigen 1 r)^t:ℝ)*normalizedCoeff v r) := by
  let a (r : ZMod N) := (↑((1-eigen 1 r)^t):ℂ)*normalizedCoeff v r
  change ‖rmsCoordinates (fun i => (synth a (ZMod.finEquiv N i)).re)‖≤blockNorm univ a
  apply (sq_le_sq₀ (norm_nonneg _) (show 0≤blockNorm univ _ from sqrt_nonneg _)).mp
  rw [rmsCoordinates_norm_sq,block_sq,div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos N)),mul_comm,←synth_parseval,←CircleGridSpectrum.fin_sum]
  exact sum_le_sum (fun i _ => sq_le_sq.mpr (by simpa using (Complex.abs_re_le_norm (synth a (ZMod.finEquiv N i)))))

def rate (d : ℕ) := shellConstant/((2:ℝ)^d)^2
private theorem rate_pos (d : ℕ) : 0<rate d := div_pos shellConstant_pos (by positivity)
private theorem rate_le_one (d : ℕ) : rate d≤1 := by
  have h : shellConstant≤1 := by unfold shellConstant;apply (div_le_iff₀ (by positivity)).mpr;nlinarith [sq_nonneg π]
  exact (div_le_self shellConstant_pos.le (one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))).trans h

/-- At every integer time, bound the exact Euler path by the sum of its
frequency bands, each decaying at its own discrete geometric rate. -/
theorem shell_distance (ho : Odd N) (v : Fin N→ℝ) (t : ℕ) :
    ‖((update N)^t) (rmsCoordinates v)‖ ≤ ∑ d ∈ range ((N+1).log2+1),
      (1-rate d)^t*blockNorm (bandSet (shell ho) d) (normalizedCoeff v) := by
  rw [iter_eq]
  apply (path_norm v t).trans
  let a := normalizedCoeff v
  let S := range ((N+1).log2+1)
  have hmap : ∀ r ∈ (univ:Finset (ZMod N)), shell ho r ∈ S := fun r _ => mem_range.mpr (Nat.lt_succ_of_le (shell_le ho r))
  have hd (d : ℕ) : ∑ r ∈ bandSet (shell ho) d, ‖(↑((1-eigen 1 r)^t):ℂ)*a r‖^2 ≤
      ((1-rate d)^t*blockNorm (bandSet (shell ho) d) a)^2 := by
    rw [mul_pow,block_sq,Finset.mul_sum]
    apply sum_le_sum;intro r hr
    have hrd := (mem_filter.mp hr).2
    have he := shell_eigen ho (τ:=1) (by norm_num) (by norm_num) r
    rw [hrd] at he
    have e0 := sub_nonneg.mpr (eigen_le_one r)
    have ef : (1-eigen 1 r)^t≤(1-rate d)^t := pow_le_pow_left₀ e0 (by dsimp [rate];linarith) t
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg e0 t),mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg e0 _) ef 2) (sq_nonneg _)
  have hnon (d : ℕ) : 0 ≤ (1-rate d)^t*blockNorm (bandSet (shell ho) d) a := mul_nonneg (pow_nonneg (sub_nonneg.mpr (rate_le_one _)) _) (sqrt_nonneg _)
  apply (sq_le_sq₀ (show 0≤blockNorm univ _ from sqrt_nonneg _) (sum_nonneg (fun d _ => hnon d))).mp
  rw [block_sq,←sum_fiberwise_of_maps_to hmap]
  exact (sum_le_sum (fun d _ => hd d)).trans (sum_sq_le_sq_sum_of_nonneg fun d _ => hnon d)

private theorem geometric_sum (d T : ℕ) : ∑ t ∈ range T, (1-rate d)^t≤min (T:ℝ) (rate d)⁻¹ := by
  have rp := rate_pos d
  have ub := rate_le_one d
  apply le_min
  · calc
      _ ≤ ∑ _t ∈ range T,(1:ℝ) := sum_le_sum (fun i _ => pow_le_one₀ (sub_nonneg.mpr ub) (by linarith))
      _ = _ := by simp
  · rw [←one_div,le_div_iff₀ rp]
    have eq (j : ℕ) : (∑ t ∈ range j, (1-rate d)^t)*rate d = 1-(1-rate d)^j := by
      induction j with
      | zero => simp
      | succ j ih => rw [sum_range_succ,add_mul,ih,pow_succ];ring
    rw [eq]
    linarith [pow_nonneg (sub_nonneg.mpr ub) T]

/-- Finite-horizon path length keeps the smaller of the stopping time and
inverse decay time in each shell. -/
theorem truncated_sum (ho : Odd N) (v : Fin N→ℝ) (T : ℕ) :
    (∑ t ∈ range T, ‖((update N)^t) (rmsCoordinates v)‖) ≤
      ∑ d ∈ range ((N+1).log2+1), min (T:ℝ) (rate d)⁻¹*blockNorm (bandSet (shell ho) d) (normalizedCoeff v) := by
  apply (sum_le_sum (fun t _ => shell_distance ho v t)).trans
  rw [sum_comm]
  apply sum_le_sum;intro d _
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (geometric_sum d T) (sqrt_nonneg _)

theorem truncatedBudget_dominates {m : ℕ} (ho : Odd N) (T : ℕ) (z : Seed m) :
    (∑ t ∈ range T, ‖((update N)^t) (rmsCoordinates (rawResidual N m z))‖) ≤ CircleTruncatedBudget.truncatedBudget ho m T z := by
  simpa only [CircleTruncatedBudget.truncatedBudget,CircleTruncatedBudget.timeWeight,rate,
    show normalizedCoeff (rawResidual N m z) = _ from funext (fun r => normalizedCoeff_raw m r z)] using
    truncated_sum ho (rawResidual N m z) T

theorem seedBudget_dominates {m : ℕ} (ho : Odd N) (T : ℕ) (z : Seed m) :
    (∑ t ∈ range T, ‖((update N)^t) (rmsCoordinates (rawResidual N m z))‖) ≤ seedBudget ho m z := by
  apply (truncated_sum ho _ T).trans
  unfold seedBudget pathBudget
  apply sum_le_sum;intro d _
  rw [show normalizedCoeff (rawResidual N m z) = _ from funext (fun r => normalizedCoeff_raw m r z)]
  exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sqrt_nonneg _)

end CircleDiscreteBudget
