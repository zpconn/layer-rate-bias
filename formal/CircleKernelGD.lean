module

public import CircleGridSpectrum
public import CircleReferenceMoments
import all CircleSpectrum
public import CircleFlowTracking
import all CircleFlowTracking
import all CircleGridSpectrum
import all CircleKernelIdentification
import all CircleTangentDrift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

/-! Discrete equal-rate population-kernel contraction with the unit Euler step. -/
public section
noncomputable section
namespace CircleKernelGD
open CircleGridSpectrum CircleKernelIdentification CircleTangentDrift Real

private local instance hp : Fact (0<π- -π) := ⟨by linarith [pi_pos]⟩

variable {N : ℕ} [NeZero N]

def gram (N : ℕ) [NeZero N] := gramOp (sampledMatrix (N:=N) 1)
def update (N : ℕ) [NeZero N] := (1 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))-gram N

private theorem entry_bound (i j : Fin N) : |sampledMatrix 1 i j|≤1 := by
  let y := gridAngle (ZMod.finEquiv N i-ZMod.finEquiv N j)
  let a := AddCircle.equivIoc (π- -π) (-π) y
  have hp : 0≤|(a:ℝ)| := abs_nonneg _
  have ha : |(a:ℝ)|≤π := abs_le.mpr ⟨a.property.1.le,by simpa using a.property.2⟩
  have eq : sampledMatrix 1 i j = polarNTK 1 |(a:ℝ)| := rfl
  rw [eq,angular_tangent 1 _ hp ha,abs_div,abs_of_pos (show 0<2*π by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  apply (abs_add_le _ _).trans
  have hsin : |sin (|(a:ℝ)|)| ≤ |(a:ℝ)| := by simpa using (abs_sin_le_abs (x:=|(a:ℝ)|))
  have hd : 0 ≤ (1+(1:ℝ))*(π-|(a:ℝ)|) := mul_nonneg (by norm_num) (sub_nonneg.mpr ha)
  rw [abs_mul,abs_of_nonneg hd]
  have hc := mul_le_mul_of_nonneg_left (abs_cos_le_one |(a:ℝ)|) hd
  linarith

/-- The complete, normalized equal-rate population operator has norm at most one. -/
theorem gram_norm_le_one : ‖gram N‖≤1 := gramOp_norm (NeZero.pos N) zero_le_one entry_bound

private theorem gram_symmetric : (gram N).toLinearMap.IsSymmetric := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun i j => sampledMatrix 1 i j / N
  change (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin N) A).toLinearMap.IsSymmetric
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.isSymmetric_toEuclideanLin_iff]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial]
  dsimp only [A]
  rw [sampledMatrix_cartesian,sampledMatrix_cartesian,cartesian_kernel_isotropic,cartesian_kernel_isotropic,abs_sub_comm]

omit [NeZero N] in
private theorem gap_le_one (hn : 3≤N) : 1/(π*(N:ℝ))^2 ≤ 1 := by
  have h : (1:ℝ)≤π*N := one_le_mul_of_one_le_of_one_le (by linarith [pi_gt_three]) (by exact_mod_cast (by omega : 1≤N))
  exact one_div_le_one_div_of_le zero_lt_one (one_le_pow₀ h) |>.trans_eq (by norm_num)

/-- The full unit-step propagator has norm at most one minus the actual circle gap. -/
theorem update_norm (hn : 3≤N) (ho : Odd N) : ‖update N‖≤1-1/(π*(N:ℝ))^2 := by
  have hs : (update N).toLinearMap.IsSymmetric := LinearMap.IsSymmetric.id.sub gram_symmetric
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro v
  have h0 := (gram N).le_opNorm v
  have hg : ‖gram N v‖≤‖v‖ := h0.trans (by simpa using mul_le_mul_of_nonneg_right (gram_norm_le_one (N:=N)) (norm_nonneg v))
  have hU : inner ℝ (gram N v) v ≤ ‖v‖^2 := (real_inner_le_norm _ _).trans (by simpa [sq] using mul_le_mul_of_nonneg_right hg (norm_nonneg v))
  have hL := gramOp_gap hn ho 1 (by norm_num) (by norm_num) v
  rw [real_inner_comm] at hL
  have hi : (update N).reApplyInnerSelf v = ‖v‖^2-inner ℝ (gram N v) v := by
    change inner ℝ (v-gram N v) v = _
    rw [inner_sub_left,real_inner_self_eq_norm_sq]
  by_cases hv : v=0
  · simpa [hv,ContinuousLinearMap.rayleighQuotient] using (gap_le_one hn)
  · show |(update N).reApplyInnerSelf v / ‖v‖^2| ≤ _
    rw [hi,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hU) (sq_nonneg _))]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mpr
    change 1/(π*(N:ℝ))^2*‖v‖^2 ≤ inner ℝ (gram N v) v at hL
    linarith

/-- Pointwise form used by capped and accepted unit-step gradient descent. -/
theorem contraction (hn : 3≤N) (ho : Odd N) (v : EuclideanSpace ℝ (Fin N)) :
    ‖v-gramOp (sampledMatrix 1) v‖≤(1-1/(π*(N:ℝ))^2)*‖v‖ :=
  ((update N).le_opNorm v).trans (mul_le_mul_of_nonneg_right (update_norm hn ho) (norm_nonneg v))

open CircleFlowTracking CircleSpectrum Finset

def gamma (N : ℕ) := aliasValue (tangentCoeff 1) (0:ZMod N)

/-- The actual population constant-mode multiplier is at least the zero
continuum Fourier coefficient and at most one at unit step. -/
theorem gamma_bounds : 3/π^2 ≤ gamma N ∧ gamma N≤1 := by
  have h0 : (3:ℝ)/π^2=tangentCoeff 1 0 := by norm_num [tangentCoeff,ntkEven]
  have hs := (tangentCoeff_summable 1 (by norm_num) (by norm_num)).indicator {k : ℤ | (k:ZMod N)=0}
  constructor
  · rw [h0,gamma,aliasValue]
    have h := hs.le_tsum 0 (fun k _ => Set.indicator_nonneg (fun j _ => tangentCoeff_nonneg (show (0:ℝ)≤1 by norm_num) j) k)
    simpa [Set.indicator_apply] using h
  · rw [gamma,←sampled_column 1 (by norm_num) (by norm_num) (0:Fin N)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr (NeZero.pos N))).mpr
    calc
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (entry_bound i 0))
      _ = _ := by simp

/-- Exact constant-row evolution on each kernel gradient-descent iterate. -/
theorem constant_mode (t : ℕ) (b : ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    rowOp (fun _ => b) (((update N)^t) v)=(1-gamma N)^t*rowOp (fun _ => b) v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ',mul_apply_eq_comp]
    change rowOp (fun _=>b) (((update N)^t) v - gram N (((update N)^t) v)) = _
    rw [map_sub,gram,gramOp_eigenrow 1 b (by norm_num) (by norm_num),ih,pow_succ']
    unfold gamma
    ring

private theorem disc_exp {x : ℝ} (hle : x≤1) (t : ℕ) : (1-x)^t ≤ exp (-(x*t)) := by
  have he : 1-x≤exp (-x) := by linarith [add_one_le_exp (-x)]
  simpa only [←exp_nat_mul, show (t:ℝ)*(-x)= -(x*t) by ring] using
    pow_le_pow_left₀ (sub_nonneg.mpr hle) he t

private theorem gamma_delay {t p : ℕ} (h : (p:ℝ)*log N ≤ gamma N*t) :
    (1-gamma N)^t≤1/(N:ℝ)^p := by
  apply (disc_exp gamma_bounds.2 t).trans
  apply (exp_le_exp.mpr (neg_le_neg h)).trans_eq
  rw [exp_neg,←log_pow,exp_log (pow_pos (Nat.cast_pos.mpr (NeZero.pos N)) _),one_div]

def short (N : ℝ) := ⌈π^2*log N⌉₊
def medium (N : ℝ) := ⌈60*log N⌉₊

/-- After the short logarithmic cap the remaining constant mode is at most N⁻³. -/
theorem short_transient : (1-gamma N)^(short N) ≤ 1/(N:ℝ)^3 := by
  apply gamma_delay
  have hl := Nat.le_ceil (π^2*log N)
  change π^2*log N≤(short N:ℝ) at hl
  calc
    (3:ℝ)*log N = (3/π^2)*(π^2*log N) := by field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ)≤3/π^2)).trans
      (mul_le_mul_of_nonneg_right gamma_bounds.1 (Nat.cast_nonneg (short N)))

/-- The medium cap has at most N⁻¹⁸ constant-mode carryover. -/
theorem medium_transient : (1-gamma N)^(medium N) ≤ 1/(N:ℝ)^18 := by
  apply gamma_delay
  have hp : π^2≤10 := by nlinarith [Real.pi_lt_d2, mul_nonneg (sub_nonneg.mpr Real.pi_lt_d2.le) (show 0≤3.15+π by positivity)]
  have hr : 3/10≤gamma N := (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp).trans gamma_bounds.1
  have ht := Nat.le_ceil (60*log N)
  change 60*log N≤(medium N:ℝ) at ht
  calc
    (18:ℝ)*log N = (3/10)*(60*log N) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤3/10)).trans
      (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (medium N)))

/-- Full grid contraction for t steps; the horizon is a stopping time that
forces the residual below N⁻³ from the stated initial RMS envelope. -/
theorem iterate_norm (hn : 3≤N) (ho : Odd N) (t : ℕ) (v : EuclideanSpace ℝ (Fin N)) :
    ‖((update N)^t) v‖≤exp (-(1/(π*(N:ℝ))^2*t))*‖v‖ := by
  have h := (norm_pow_le (update N) t).trans (pow_le_pow_left₀ (norm_nonneg _) (update_norm hn ho) t)
  exact (((update N)^t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (h.trans (disc_exp (gap_le_one hn) t)) (norm_nonneg v))

theorem horizon_fit (hn : 3≤N) (ho : Odd N) (v : EuclideanSpace ℝ (Fin N))
    (init : ‖v‖≤2*sqrt (12*N)) : ‖((update N)^(horizon N)) v‖≤1/(N:ℝ)^3 := by
  let scale := 2*sqrt (12*(N:ℝ))*(N:ℝ)^3
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hs : 1≤scale := by
    have hN : (3:ℝ)≤N := by exact_mod_cast hn
    have hs1 : 1≤sqrt (12*(N:ℝ)) := one_le_sqrt.mpr (by linarith)
    exact one_le_mul_of_one_le_of_one_le (show 1≤2*sqrt (12*(N:ℝ)) by linarith) (one_le_pow₀ (by exact_mod_cast (by omega : 1≤N)))
  have htime := Nat.le_ceil (2*π^2*(N:ℝ)^2*log scale)
  change 2*π^2*(N:ℝ)^2*log scale ≤ (horizon N:ℝ) at htime
  have hd : log scale ≤ 1/(π*(N:ℝ))^2*(horizon N:ℝ) := by
    rw [one_div_mul_eq_div,le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg π) (sq_nonneg (N:ℝ))) (log_nonneg hs)]
  have he := (exp_le_exp.mpr (neg_le_neg hd)).trans_eq (show exp (-log scale)=1/scale by rw [exp_neg,exp_log (by linarith),one_div])
  apply (iterate_norm hn ho _ _).trans
  apply (mul_le_mul he init (norm_nonneg _) (by dsimp [scale];positivity)).trans_eq
  unfold scale
  field_simp [sqrt_ne_zero'.mpr (show 0<12*(N:ℝ) by positivity)]

/-- Every fixed polynomial accuracy is eventually met by the constant mode
at H; the finite-grid bound already holds whenever p≤6N². -/
theorem horizon_transient (hn : 3≤N) (p : ℕ) (hq : p≤6*N^2) :
    (1-gamma N)^(horizon N) ≤ 1/(N:ℝ)^p := by
  apply gamma_delay
  have nh : (3:ℝ)≤N := by exact_mod_cast hn
  have hp : 0<(N:ℝ) := by linarith
  have hs1 : 1≤sqrt (12*(N:ℝ)) := one_le_sqrt.mpr (by linarith)
  have hpN : (1:ℝ)≤N := by linarith
  let scale := 2*sqrt (12*(N:ℝ))*(N:ℝ)^3
  have hpow : (N:ℝ)≤(N:ℝ)^3 := by simpa using (pow_le_pow_right₀ hpN (by decide : 1≤3))
  have hs : (N:ℝ)≤scale := hpow.trans (le_mul_of_one_le_left (by positivity) (show 1≤2*sqrt (12*(N:ℝ)) by linarith))
  have hl : log N≤log scale := log_le_log hp hs
  have hq' : (p:ℝ)≤6*(N:ℝ)^2 := by exact_mod_cast hq
  have ht : 2*π^2*(N:ℝ)^2*log scale≤(horizon N:ℝ) := Nat.le_ceil _
  calc
    _ ≤ (6*(N:ℝ)^2)*log N := mul_le_mul_of_nonneg_right hq' (log_nonneg hpN)
    _ ≤ (6*(N:ℝ)^2)*log scale := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = (3/π^2)*(2*π^2*(N:ℝ)^2*log scale) := by field_simp; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤3/π^2)).trans
      (mul_le_mul_of_nonneg_right gamma_bounds.1 (Nat.cast_nonneg _))

open CircleEscapeBridge CircleReferenceMoments Filter Topology MeasureTheory

/-- Coefficient of the exact stopped equal-rate fixed-kernel trajectory. -/
def stoppedWeight (n T : ℕ) := weight 1 n*(1-(1-gamma (n+1))^T)

theorem stopped_reference_moments (n m T : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) :
    (∫ ω, reference (n+1) m (stoppedWeight n T) ω ∂seedLaw m) = stoppedWeight n T ∧
    ProbabilityTheory.variance (reference (n+1) m (stoppedWeight n T)) (seedLaw m) =
      c0*(1-stoppedWeight n T)^2+(stoppedWeight n T)^2*S n :=
  reference_moments n m hn ho hm _

/-- All caps at least as long as S share the equal-rate constants, independently
of the chosen positive finite network width. -/
theorem stopped_reference_limits (n m T : ℕ → ℕ) (growth : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, 0<m i)
    (cap : ∀ i, short ((n i:ℝ)+1) ≤ T i) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*(1-∫ ω, reference (n i+1) (m i) (stoppedWeight (n i) (T i)) ω ∂seedLaw (m i)))
      atTop (𝓝 (π^2/36)) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (reference (n i+1) (m i) (stoppedWeight (n i) (T i))) (seedLaw (m i)))
      atTop (𝓝 (7*π^2/1620)) := by
  let M (i : ℕ) := (n i:ℝ)+1
  let e (i : ℕ) := (1-gamma (n i+1))^(T i)
  let b (i : ℕ) := weight 1 (n i)
  let w (i : ℕ) := stoppedWeight (n i) (T i)
  have mn (i : ℕ) : M i≠0 := by dsimp [M];positivity
  have mp (i : ℕ) : 0<M i := by dsimp [M];positivity
  have e₀ (i : ℕ) : 0≤e i := pow_nonneg (sub_nonneg.mpr gamma_bounds.2) _
  have eB (i : ℕ) : e i≤1/(M i)^3 := by
    have g := gamma_bounds (N:=n i+1)
    have u : 1-gamma (n i+1) ≤ 1 := by linarith [g.1,show (0:ℝ)≤3/π^2 by positivity]
    exact (pow_le_pow_of_le_one (sub_nonneg.mpr g.2) u (cap i)).trans (by simpa [M] using (short_transient (N:=n i+1)))
  have iM : Tendsto (fun i => 1/M i) atTop (𝓝 0) := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp growth
  have se : Tendsto (fun i => M i^2*e i) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (e₀ i)) (fun i => (mul_le_mul_of_nonneg_left (eB i) (sq_nonneg _)).trans_eq ?_) iM
    field_simp [mn i]
  have el : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero e₀ eB
    simpa [one_div] using iM.pow 3
  have bl : Tendsto b atTop (𝓝 1) := (weight_limit 1 (by norm_num)).comp growth
  have wl : Tendsto w atTop (𝓝 1) := by simpa [w,b,e,stoppedWeight] using bl.mul ((tendsto_const_nhds (x:=(1:ℝ))).sub el)
  have hbi := (bias_limit 1 (by norm_num)).comp growth
  have bias : Tendsto (fun i => M i^2*(1-w i)) atTop (𝓝 (π^2/36)) := by
    convert hbi.add (se.mul bl) using 2
    · dsimp [Function.comp_def,M,w,stoppedWeight,e,b];ring
    · ring
  have moments (i : ℕ) := stopped_reference_moments (n i) (m i) (T i) (hn i) (ho i) (hm i)
  simp_rw [fun i => (moments i).1,fun i => (moments i).2]
  refine ⟨bias,?_⟩
  have sv := scaledS_limit.comp growth
  convert ((bias.pow 2).const_mul c0).add ((wl.pow 2).mul sv) using 2
  · dsimp [w,M,S,rp,Function.comp_def]
    field_simp [mn _]
  · unfold c0
    field_simp
    ring

end CircleKernelGD
