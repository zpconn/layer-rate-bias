module

public import CirclePairedSecondOrder
import all CirclePairedSecondOrder
public import CircleGDLimits
public import CircleSharpGDMoments
import all CircleGDLimits
import all CircleSharpGDMoments
import all CircleKernelGD
import all CircleComparison
import all CircleGaussianTracking
import all CircleResidualSpectrum
import all CircleEscapeBridge
import all CirclePairedCoefficient
import all CircleSpectrum
import all CircleShortGDTails
import all CircleDiscreteMoments
import all CircleCapMoments
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The exactly rounded early-cap transient controls the RMS error against the
fully converged reference. -/
@[expose] public section
noncomputable section
namespace CircleShortEquivalent
open Real MeasureTheory ProbabilityTheory Filter Set Asymptotics
open CircleSpectrum CircleKernelGD CircleGDLimits CircleEscapeBridge CirclePairedCoefficient
  CircleSeedIntegrability CircleDiscreteMoments CircleCapMoments CircleSharpGDMoments
open scoped Topology
set_option maxHeartbeats 800000

def base := 1-3/π^2
def alpha := -π^2*log base
def D (n : ℕ) := (n:ℝ)+1
def scale (n : ℕ) := (D n)^(-alpha)
def S (n : ℕ) := short (D n)
def decay (n : ℕ) := (1-gamma (n+1))^(S n)

theorem base_bounds : 0<base ∧ base<1 := by
  have p : 9<π^2 := by nlinarith [pi_gt_three,sq_nonneg (π-3)]
  unfold base
  constructor
  · have := (div_lt_one (by positivity : 0<π^2)).mpr (show 3<π^2 by linarith)
    linarith
  · have : 0<(3:ℝ)/π^2 := by positivity
    linarith

theorem alpha_bounds : 3<alpha ∧ alpha<5 := by
  let q := base
  have pos : 0<q := base_bounds.1
  have ne : q≠1 := base_bounds.2.ne
  have p : 9<π^2 := by nlinarith [pi_gt_three,sq_nonneg (π-3)]
  have left := log_lt_sub_one_of_pos pos ne
  have right := log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [log_inv] at right
  have id : π^2*(1-q)=3 := by dsimp [q,base];field_simp;ring
  have low : 3<π^2*(-log q) := by
    have := mul_lt_mul_of_pos_left (by linarith only [left] : 1-q < -log q) (sq_pos_of_pos pi_pos)
    linarith
  have qlarge : 3/5<q := by
    dsimp [q,base]
    have := (div_lt_iff₀ (sq_pos_of_pos pi_pos)).2 (by linarith only [p] : 3<(1-3/5)*π^2)
    linarith
  have hi := mul_le_mul_of_nonneg_left right (sq_nonneg π)
  have eq : π^2*(q⁻¹-1)=3/q := by field_simp; linarith only [id]
  rw [eq] at hi
  have := (div_lt_iff₀ pos).mpr (by linarith only [qlarge] : 3<5*q)
  change 3 < -π^2*log q ∧ -π^2*log q<5
  constructor <;> linarith only [low,hi,this]

private theorem gamma_eq (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    gamma (n+1)=3/π^2+U 1 n := by
  rw [gamma,CircleGridSpectrum.constant_alias_eq hn ho 1 (by norm_num) (by norm_num),U_eq_alias_sum]
  push_cast
  norm_num [k0]

private theorem rounded (n : ℕ) : base*scale n ≤ base^(S n) ∧ base^(S n) ≤ scale n := by
  let t := π^2*log (D n)
  have d : 1≤D n := by dsimp [D];linarith [show 0≤(n:ℝ) by positivity]
  have dp : 0<D n := zero_lt_one.trans_le d
  have tt : 0≤t := mul_nonneg (sq_nonneg _) (log_nonneg d)
  have h₁ : t≤(S n:ℝ) := Nat.le_ceil _
  have h₂ : (S n:ℝ)≤t+1 := (Nat.ceil_lt_add_one tt).le
  have e : base^t=scale n := by
    rw [scale,rpow_def_of_pos base_bounds.1,rpow_def_of_pos dp]
    congr 1; dsimp [t,alpha];ring
  rw [←rpow_natCast,←e]
  constructor
  · have := rpow_le_rpow_of_exponent_ge base_bounds.1 base_bounds.2.le h₂
    simpa only [rpow_add base_bounds.1, rpow_one, mul_comm] using this
  · exact rpow_le_rpow_of_exponent_ge base_bounds.1 base_bounds.2.le h₁

/-- The ceiling at the early cap costs at most one factor of the limiting
multiplier. The finite-grid alias perturbs the full power by a bounded factor. -/
theorem decay_bounds (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    ∀ᶠ i in atTop, base/2*scale (n i) ≤ decay (n i) ∧ decay (n i) ≤ scale (n i) := by
  have u := (scaledU_limit 1 (by norm_num)).comp grow
  have dg : Tendsto (fun i => D (n i)) atTop atTop := CircleComparison.grown n grow
  filter_upwards [u.eventually_le_const (by norm_num : (1:ℝ)/12<1),
    dg.eventually (eventually_ge_atTop (34/base))] with i u1 big
  let k := n i
  have k1 : 1≤D k := by dsimp [D];linarith [show 0≤(k:ℝ) by positivity]
  have kp : 0<D k := zero_lt_one.trans_le k1
  have ga :=  gamma_eq k (hn i) (ho i)
  have up : 0≤U 1 k := by linarith only [ga,(gamma_bounds (N:=k+1)).1]
  have ub : U 1 k ≤ 1/(D k)^2 := by
    change (1/(D k)^2)*scaledU 1 k ≤ _
    exact mul_le_of_le_one_right (by positivity) u1
  have t : (S k:ℝ)≤17*D k := by
    simpa only [S,D,short,CircleShortGDTails.earlyCap,Nat.cast_add,Nat.cast_one] using
      early_le (k+1) (by exact_mod_cast Nat.succ_pos k)
  have hq := base_bounds.1
  have diff : 1-gamma (k+1)=base-U 1 k := by rw [ga];unfold base;ring
  have r : U 1 k/base ≤ 1 := (div_le_one hq).mpr (by linarith only [diff,(gamma_bounds (N:=k+1)).2])
  have sr : (S k:ℝ)*(U 1 k/base)≤1/2 := by
    apply (mul_le_mul t (div_le_div_of_nonneg_right ub hq.le) (div_nonneg up hq.le) (by positivity)).trans
    have h : 34 ≤ D k*base := (div_le_iff₀ hq).mp big
    field_simp [kp.ne',hq.ne']
    linarith only [h]
  have bern := one_add_mul_le_pow (by linarith only [r] : -2 ≤ -(U 1 k/base)) (S k)
  have mult : 1/2 ≤ (1-(U 1 k/base))^(S k) := by
    rw [←sub_eq_add_neg] at bern
    linarith only [bern,sr]
  have exactPow : decay k = base^(S k)*(1-U 1 k/base)^(S k) := by
    rw [decay,diff,←mul_pow]
    congr 1;field_simp
  have ceiling := rounded k
  refine ⟨?_,?_⟩
  · calc
      _ = base*scale k*(1/2) := by ring
      _ ≤ base^(S k)*(1-U 1 k/base)^(S k) := mul_le_mul ceiling.1 mult (by norm_num) (pow_nonneg hq.le _)
      _ = _ := exactPow.symm
  · apply (pow_le_pow_left₀ (sub_nonneg.mpr (gamma_bounds (N:=k+1)).2)
      (show 1-gamma (k+1)≤base by rw [diff];linarith) (S k)).trans ceiling.2

open CircleResidualSpectrum

def X (n : ℕ) := score (n+1) (Width n)
def Z (n : ℕ) := reference (n+1) (Width n) (weight 1 n)
def ZS (n : ℕ) := reference (n+1) (Width n) (stoppedWeight n (S n))
def rms {n : ℕ} (μ : Measure (Seed (Width n))) (Y : Seed (Width n) → ℝ) :=
  sqrt (∫ z, (Y z-Z n z)^2 ∂μ)

private theorem score_mean (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) :
    ∫ z, X n z ∂seedLaw (Width n) = 1 := by
  let R := reference (n+1) (Width n)
  have eq : X n = R 1-R 0 := by funext z; simp only [X,R,score,reference,Pi.sub_apply];ring
  have h b := (CircleReferenceMoments.reference_moments n (Width n) hn odd (pow_pos (Nat.succ_pos _) _) b).1
  rw [eq]
  simp only [Pi.sub_apply,R]
  rw [integral_sub ((reference_memLp _ _ 1 2 (by norm_num)).integrable one_le_two)
    ((reference_memLp _ _ 0 2 (by norm_num)).integrable one_le_two),h 1,h 0,sub_zero]

private theorem score_four (n : ℕ) (hn : 3≤n+1) :
    MemLp (X n) 4 (seedLaw (Width n)) ∧ lpNorm (X n) 4 (seedLaw (Width n))≤modeConstant := by
  let f := initialCoeff (n+1) (Width n) 0
  let μ := seedLaw (Width n)
  have hf := initialCoeff_uniform (m:=Width n) (pow_pos (Nat.succ_pos _) _) (0:ZMod (n+1))
  have eq : X n = fun z => -Complex.reCLM (f z) := by
    funext z;simpa [f,X] using (congrArg Neg.neg (zero_mode hn z)).symm
  refine ⟨by rw [eq]; exact (hf.1.continuousLinearMap_comp Complex.reCLM).neg,?_⟩
  have le' (z : Seed (Width n)) : ‖X n z‖ ≤ ‖f z‖ := by
    rw [eq,norm_neg];exact Complex.abs_re_le_norm _
  exact (lpNorm_mono_real hf.1.norm le').trans ((lpNorm_norm hf.1.aestronglyMeasurable _).le.trans hf.2)

private theorem score_mass (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    1 ≤ ∫ z, (X n z)^2 ∂seedLaw (Width n) := by
  have h := variance_nonneg (X n) (seedLaw (Width n))
  have mem : MemLp (X n) 2 (seedLaw (Width n)) := (score_bound hn (m:=Width n) (pow_pos (Nat.succ_pos _) _)).1
  rw [variance_eq_sub mem,score_mean n hn ho] at h
  simp only [Pi.pow_apply,one_pow,sub_nonneg] at h
  exact h

private theorem seed_score (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    1/2 ≤ lpNorm (X n) 2 (seedLaw (Width n)) ∧ lpNorm (X n) 2 (seedLaw (Width n))≤modeConstant := by
  have b := score_bound hn (m:=Width n) (pow_pos (Nat.succ_pos _) _)
  refine ⟨?_,b.2⟩
  rw [← rms_of_mem _ (show MemLp (X n) 2 _ from b.1)]
  exact (by norm_num : (1:ℝ)/2≤sqrt 1).trans (sqrt_le_sqrt (score_mass n hn ho))

private theorem gaussian_score_limit (n : ℕ → ℕ) (grow : Tendsto n atTop atTop) :
    Tendsto (fun i => 1+c0+CircleSpectrum.S (n i)) atTop (𝓝 (1+c0)) := by
  have hi := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow
  have r : Tendsto (fun i => rp 4 (n i)) atTop (𝓝 0) := by
    simpa [rp,div_pow] using hi.pow 4
  have sr := r.mul (scaledS_limit.comp grow)
  simpa only [CircleSpectrum.S,Function.comp_def,zero_mul,add_zero] using sr.const_add (1+c0)

private theorem score_sq_formula (n : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) :
    (∫ z, X n z^2 ∂seedLaw (Width n))=1+c0+CircleSpectrum.S n := by
  have mem := (score_bound (m:=Width n) hn (pow_pos (Nat.succ_pos _) _)).1
  have eq := CirclePairedSecondOrder.score_rms n (Width n) hn ho (pow_pos (Nat.succ_pos _) _)
  change lpNorm (X n) 2 _ = _ at eq
  rw [←rms_of_mem _ (show MemLp (X n) 2 _ from mem)] at eq
  have p : 0≤1+c0+CircleSpectrum.S n := by
    unfold c0 CircleSpectrum.S scaledS rp
    positivity
  exact (sq_sqrt (integral_nonneg fun z => sq_nonneg (X n z))).symm.trans
    ((congrArg (fun t:ℝ => t^2) eq).trans (sq_sqrt p))

private theorem accepted_score_limit (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    Tendsto (fun i => lpNorm (X (n i)) 2 (acceptedLaw (n i))) atTop (𝓝 (sqrt (1+c0))) := by
  let K := modeConstant
  let μ (i : ℕ) := seedLaw (Width (n i))
  let A (i : ℕ) := screen (n i+1) (Width (n i))
  let p (i : ℕ) := (μ i).real (A i)
  have inv : Tendsto (fun i => 1/D (n i)) atTop (𝓝 0) := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow
  have ma (i : ℕ) : MeasurableSet (A i) := screen_measurable _ _ (by have := hn i;omega) (ho i) (pow_pos (Nat.succ_pos _) _)
  have pq (i : ℕ) : (μ i).real (A i)ᶜ≤(1/D (n i))^158 := by
    simpa only [D,μ,A,Width,Nat.cast_add,Nat.cast_one,one_div,inv_pow] using reject_pow (n i+1) (hn i) (ho i)
  have ql : Tendsto (fun i => (μ i).real (A i)ᶜ) atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg) pq (by simpa using inv.pow 158)
  have pl : Tendsto p atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x:=(1:ℝ))).sub ql using 2 with i
    · rw [measureReal_compl (ma i),probReal_univ];dsimp [p];ring
    · ring
  have hs (i : ℕ) : MemLp (X (n i)) 2 (μ i) := (score_bound (m:=Width (n i)) (by have := hn i;omega) (pow_pos (Nat.succ_pos _) _)).1
  have tail : Tendsto (fun i => ∫ z in (A i)ᶜ, X (n i) z^2 ∂μ i) atTop (𝓝 0) := by
    refine squeeze_zero (fun i => integral_nonneg fun _ => sq_nonneg _) (g:=fun i => K^2*sqrt ((μ i).real (A i)ᶜ)) ?_ (by simpa using ql.sqrt.const_mul (K^2))
    intro i
    have hm := score_four (n i) (by have := hn i;omega)
    have hs2 : MemLp (fun z => X (n i) z^2) 2 (μ i) := by
      apply (memLp_two_iff_integrable_sq (hm.1.aestronglyMeasurable.pow 2)).2
      simpa only [Pi.pow_apply,←pow_mul,Nat.reduceMul,Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hm.1.integrable_norm_pow' (p:=4)
    have ee := CircleMoment.exceptional_second_moment hs2 (A i)ᶜ
    rw [CircleGaussianTracking.fourth_integral hm.1,show lpNorm (X (n i)) 4 (μ i)^4=(lpNorm (X (n i)) 4 (μ i)^2)^2 by ring,sqrt_sq (sq_nonneg _)] at ee
    exact ee.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ lpNorm_nonneg hm.2 2) (sqrt_nonneg _))
  have total : Tendsto (fun i => ∫ z, X (n i) z^2 ∂μ i) atTop (𝓝 (1+c0)) :=
    (gaussian_score_limit n grow).congr fun i => (score_sq_formula _ (by have := hn i;omega) (ho i)).symm
  have on : Tendsto (fun i => ∫ z in A i, X (n i) z^2 ∂μ i) atTop (𝓝 (1+c0)) := by
    convert total.sub tail using 2 with i
    · rw [←integral_add_compl (ma i) (hs i).integrable_sq];ring
    · ring
  have lim := on.div pl (by norm_num : (1:ℝ)≠0)
  simp only [div_one] at lim
  apply lim.sqrt.congr
  intro i
  have nz := accept_pos (n:=n i) (by have := hn i;omega) (ho i)
  have ha : MemLp (X (n i)) 2 (acceptedLaw (n i)) :=
    ((hs i).restrict (s:=A i)).smul_measure (by simpa using nz)
  rw [←rms_of_mem _ ha]
  congr 1
  change _/p i=(∫ z, X (n i) z^2 ∂((μ i) (A i))⁻¹ • (μ i).restrict (A i))
  rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,div_eq_inv_mul];rfl

private theorem accepted_score (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    ∀ᶠ i in atTop, 1/2≤lpNorm (X (n i)) 2 (acceptedLaw (n i)) ∧
      lpNorm (X (n i)) 2 (acceptedLaw (n i)) ≤ 2 := by
  have lim := accepted_score_limit n grow hn ho
  have h : 0<c0 := by unfold c0; positivity
  have h' : c0<1 := (div_lt_one (sq_pos_of_pos pi_pos)).2 (by nlinarith [pi_gt_three,sq_nonneg (π-3)])
  exact (lim.eventually_const_le (lt_sqrt_of_sq_lt (by linarith : (1/2:ℝ)^2<1+c0))).and
    (lim.eventually_le_const ((sqrt_lt' (by norm_num : (0:ℝ)<2)).mpr (by linarith)))

private theorem gap_eq (n : ℕ) (μ : Measure (Seed (Width n))) :
    lpNorm (ZS n - Z n) 2 μ = weight 1 n*decay n*lpNorm (X n) 2 μ := by
  have eq : ZS n-Z n = (-(weight 1 n*decay n)) • X n := by
    funext z
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ZS,Z,stoppedWeight,decay,X,score,reference]
    ring
  have w := (CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)).1
  have e : 0≤decay n := pow_nonneg (sub_nonneg.mpr (gamma_bounds (N:=n+1)).2) _
  rw [eq,lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_neg,abs_of_nonneg (mul_nonneg w e)]

private theorem scale_positive (n : ℕ) : 0<scale n := rpow_pos_of_pos (by dsimp [D];positivity) _

private theorem scale_dominates (n : ℕ → ℕ) (grow : Tendsto n atTop atTop) (C : ℝ) :
    Tendsto (fun i => C/(D (n i))^15/scale (n i)) atTop (𝓝 0) := by
  have d := CircleComparison.grown n grow
  have a : 0<15-alpha := by linarith only [alpha_bounds.2]
  have lim := ((tendsto_rpow_neg_atTop a).comp d).const_mul C
  convert lim using 2 with i
  · let x := D (n i)
    have xp : 0<x := by dsimp [x,D];positivity
    change C/x^15/(x^(-alpha))=C*x^(-(15-alpha))
    rw [rpow_neg xp.le,div_inv_eq_mul,show -(15-alpha)=alpha-(15:ℕ) by push_cast;ring,
      rpow_sub_natCast xp.ne']
    ring
  · ring

/-- The exact finite-grid kernel stopping term, including the integer cap. -/
def leading (n : ℕ) := weight 1 n*decay n*sqrt (1+c0+CircleSpectrum.S n)

private def EndpointResult (n : ℕ → ℕ) (μ : (i : ℕ)→Measure (Seed (Width (n i))))
    (Y : (i : ℕ) → Seed (Width (n i))→ℝ) : Prop :=
  ((fun i => rms (μ i) (Y i)) =Θ[atTop] (fun i => scale (n i))) ∧
  ((fun i => rms (μ i) (Y i)) ~[atTop] (fun i => leading (n i)))

private theorem endpoint_theta (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1))
    (μ : (i : ℕ) → Measure (Seed (Width (n i)))) (Y : (i : ℕ) → Seed (Width (n i)) → ℝ)
    (ym : ∀ i, MemLp (Y i) 2 (μ i)) (zm : ∀ i, MemLp (Z (n i)) 2 (μ i))
    (sm : ∀ i, MemLp (ZS (n i)) 2 (μ i)) (K C : ℝ)
    (sc : ∀ᶠ i in atTop, 1/2 ≤ lpNorm (X (n i)) 2 (μ i) ∧ lpNorm (X (n i)) 2 (μ i) ≤ K)
    (xl : Tendsto (fun i => lpNorm (X (n i)) 2 (μ i)) atTop (𝓝 (sqrt (1+c0))))
    (err : ∀ i, sqrt (∫ z, (Y i z-ZS (n i) z)^2 ∂μ i) ≤ C/(D (n i))^15) :
    EndpointResult n μ Y := by
  have w := (weight_limit 1 (by norm_num)).comp grow
  have small := (scale_dominates n grow C).eventually_le_const (by linarith [base_bounds.1] : 0<base/16)
  have estimates : ∀ᶠ i in atTop, base/16*scale (n i) ≤ rms (μ i) (Y i) ∧
      rms (μ i) (Y i) ≤ (K+base/16)*scale (n i) := by
    filter_upwards [decay_bounds n grow hn ho,sc,w.eventually_const_le (by norm_num : (1:ℝ)/2<1),small]
      with i de xx ww ep
    let k := n i
    let gap := lpNorm (ZS k-Z k) 2 (μ i)
    have sp := scale_positive k
    have w1 := (CircleGaussianTracking.weight_bounds k (τ:=1) (by norm_num)).2
    have er : lpNorm (Y i-ZS k) 2 (μ i) ≤ base/16*scale k := by
      rw [←rms_of_mem _ ((ym i).sub (sm i))]
      exact (err i).trans ((div_le_iff₀ sp).mp ep)
    have lo : base/8*scale k≤gap := by
      rw [show gap= _ from gap_eq k (μ i)]
      have nd := (mul_nonneg (by linarith [base_bounds.1] : 0≤base/2) sp.le)
      change 1/2≤weight 1 k at ww
      have w0 := (by norm_num : (0:ℝ)≤1/2).trans ww
      have lwd : (1/2)*(base/2*scale k)≤weight 1 k*decay k := mul_le_mul ww de.1 nd w0
      have := mul_le_mul lwd xx.1 (by norm_num : (0:ℝ)≤1/2) (mul_nonneg w0 (nd.trans de.1))
      linarith only [this]
    have high : gap≤K*scale k := by
      rw [show gap= _ from gap_eq k (μ i)]
      have de0 : 0≤decay k := pow_nonneg (sub_nonneg.mpr (gamma_bounds (N:=k+1)).2) _
      have h := mul_le_mul ((mul_le_of_le_one_left de0 w1).trans de.2) xx.2 lpNorm_nonneg sp.le
      simpa only [mul_comm] using h
    have l := lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (f:=ZS k) (g:=Y i) (h:=Z k) (sm i) (ym i) (by norm_num : 1≤(2:ENNReal))
    rw [lpNorm_sub_comm (ZS k) (Y i)] at l
    have r := lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (f:=Y i) (g:=ZS k) (h:=Z k) (ym i) (sm i) (by norm_num : 1≤(2:ENNReal))
    change gap ≤ _ at l
    change _ ≤ _+gap at r
    have rmsid : rms (μ i) (Y i)=lpNorm (Y i-Z k) 2 (μ i) := rms_of_mem _ ((ym i).sub (zm i))
    rw [rmsid]
    constructor <;> linarith only [lo,high,l,r,er]
  have theta : (fun i => rms (μ i) (Y i)) =Θ[atTop] (fun i => scale (n i)) := by
    constructor
    · refine isBigO_iff.mpr ⟨K+base/16,estimates.mono fun i h => ?_⟩
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _),abs_of_nonneg (scale_positive (n i)).le,rms] using h.2
    · refine isBigO_iff.mpr ⟨16/base,estimates.mono fun i h => ?_⟩
      simp only [Real.norm_eq_abs,abs_of_nonneg (scale_positive (n i)).le,rms,abs_of_nonneg (sqrt_nonneg _)]
      have hb := base_bounds.1
      have hh := (le_div_iff₀ (by linarith : 0<base/16)).mpr (by simpa only [mul_comm] using h.1)
      change scale (n i) ≤ _*rms (μ i) (Y i)
      exact hh.trans_eq (by ring)

  let g (i : ℕ) := lpNorm (ZS (n i)-Z (n i)) 2 (μ i)
  have diff (i : ℕ) : |g i-rms (μ i) (Y i)|≤C/(D (n i))^15 := by
    have rev := CirclePairedSecondOrder.reverse_norm (μ i) ((sm i).sub (zm i)) ((ym i).sub (zm i))
    rw [sub_sub_sub_cancel_right,lpNorm_sub_comm (ZS (n i)) (Y i)] at rev
    have rhs : lpNorm (Y i-ZS (n i)) 2 (μ i) ≤ C/(D (n i))^15 := by
      rw [←rms_of_mem _ ((ym i).sub (sm i))];exact err i
    have ey : rms (μ i) (Y i)=lpNorm (Y i-Z (n i)) 2 (μ i) := rms_of_mem _ ((ym i).sub (zm i))
    rw [ey]; exact rev.trans rhs
  have gg : g ~[atTop] (fun i => rms (μ i) (Y i)) := by
    apply IsLittleO.isEquivalent
    apply IsLittleO.trans_isBigO (g:=fun i => scale (n i)) _ theta.2
    apply isLittleO_iff.mpr
    intro e he
    filter_upwards [(scale_dominates n grow C).eventually_le_const he] with i h
    change ‖g i-rms (μ i) (Y i)‖ ≤ e*‖scale (n i)‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (scale_positive _).le]
    exact (diff i).trans ((div_le_iff₀ (scale_positive _)).mp h)
  have nonzero : sqrt (1+c0)≠0 := (sqrt_pos.mpr (by unfold c0;positivity)).ne'
  have xeq : (fun i => lpNorm (X (n i)) 2 (μ i)) ~[atTop] (fun i => sqrt (1+c0+CircleSpectrum.S (n i))) :=
    isEquivalent_of_tendsto_one (by simpa only [div_self nonzero] using xl.div (gaussian_score_limit n grow).sqrt nonzero)
  have e := (IsEquivalent.refl (l:=atTop) (u:=fun i => weight 1 (n i)*decay (n i))).mul xeq
  have e' : g ~[atTop] (fun i => leading (n i)) := by
    simpa only [g,gap_eq,leading,Pi.mul_def] using e
  exact ⟨theta,gg.symm.trans e'⟩

private theorem common_cap (n : ℕ) : S n ≤ 385*(n+1)^3 :=
  (benchmark_times n).1.trans (benchmark_times n).2.1

private theorem shape_bound (n : ℕ) :
    errorConstant*shape (n+1) (S n)/((n+1:ℕ):ℝ)^16 ≤ errorConstant/(D n)^15 := by
  have dp : 0<D n := by dsimp [D];positivity
  have h : shape (n+1) (S n)≤D n := (min_le_left _ _).trans_eq (by simp [D])
  have eq : ((n+1:ℕ):ℝ)=D n := by simp [D]
  rw [eq]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h constant_nonneg) (by positivity)).trans_eq (by field_simp)

private theorem denominator_floor (n : ℕ) (hn : 12000000≤n+1) :
    1/2 ≤ sqrt (1-exp (-((Width n:ℕ):ℝ)/240)) := by
  have m : 240≤Width n := by
    apply (by omega : 240≤n+1).trans
    simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1≤32))
  have x : (1:ℝ)≤(Width n:ℝ)/240 := by
    have h : (240:ℝ)≤Width n := by exact_mod_cast m
    linarith
  have e : 2≤exp ((Width n:ℝ)/240) := by linarith [add_one_le_exp ((Width n:ℝ)/240)]
  have neg : exp (-((Width n:ℕ):ℝ)/240)≤1/2 := by
    rw [neg_div,exp_neg,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) e
  apply le_sqrt_of_sq_le
  linarith

/-- The fully converged matched-reference RMS has the same sharp power law
under unconditioned ordinary GD, unconditioned capped GD, and ordinary GD
conditioned on pretraining curvature acceptance. -/
private theorem actual_short_results (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    EndpointResult n (fun i => seedLaw (Width (n i))) (fun i => fixed (n i) (S (n i))) ∧
    EndpointResult n (fun i => seedLaw (Width (n i))) (fun i => capped (n i) (S (n i))) ∧
    EndpointResult n (fun i => acceptedLaw (n i)) (fun i => fixed (n i) (S (n i))) := by
  have large (i : ℕ) : 3≤n i+1 := by have := hn i;omega
  have sc := Filter.Eventually.of_forall (f:=atTop) (fun i => seed_score (n i) (large i) (ho i))
  let μ (i : ℕ) := seedLaw (Width (n i))
  have fy (i : ℕ) : MemLp (fixed (n i) (S (n i))) 2 (μ i) := trained_memLp _ _ _ 1 2 (by norm_num)
  have cy (i : ℕ) := cap_mem (hn i) (ho i) (common_cap (n i))
  have z (i : ℕ) : MemLp (Z (n i)) 2 (μ i) := reference_memLp _ _ _ 2 (by norm_num)
  have s (i : ℕ) : MemLp (ZS (n i)) 2 (μ i) := reference_memLp _ _ _ 2 (by norm_num)
  have cerr (i : ℕ) : sqrt (∫ x, (capped (n i) (S (n i)) x-ZS (n i) x)^2 ∂μ i) ≤ errorConstant/(D (n i))^15 :=
    (capped_stopped_sharp (n i) (S (n i)) (hn i) (ho i) (common_cap (n i))).trans (shape_bound (n i))
  have xl : Tendsto (fun i => lpNorm (X (n i)) 2 (μ i)) atTop (𝓝 (sqrt (1+c0))) :=
    (gaussian_score_limit n grow).sqrt.congr (fun i => (CirclePairedSecondOrder.score_rms (n i) (Width (n i))
      (large i) (ho i) (pow_pos (Nat.succ_pos _) _)).symm)
  refine ⟨endpoint_theta n grow large ho μ _ fy z s modeConstant errorConstant sc xl ?_,
    endpoint_theta n grow large ho μ _ cy z s modeConstant errorConstant sc xl cerr,?_⟩
  · intro i
    have h := ordinary_short_sharp (n i) (hn i) (ho i)
    simpa only [fixed,ZS,Width,μ,CircleShortGDTails.earlyCap,CircleKernelGD.short,CircleShortEquivalent.S,D,Nat.cast_add,Nat.cast_one] using
      h.trans (by simpa only [CircleShortGDTails.earlyCap,CircleKernelGD.short,CircleShortEquivalent.S,D,Nat.cast_add,Nat.cast_one] using shape_bound (n i))
  · have restrictMem (i : ℕ) (f : Seed (Width (n i))→ℝ) (hm : MemLp f 2 (μ i)) :
        MemLp f 2 (acceptedLaw (n i)) := by
      have nz := accept_pos (n:=n i) (by have := hn i;omega) (ho i)
      exact (hm.restrict (s:=screen (n i+1) (Width (n i)))).smul_measure (by simpa only [ne_eq,ENNReal.inv_eq_top] using nz)
    apply endpoint_theta n grow large ho _ _ (fun i => restrictMem i _ (fy i)) (fun i => restrictMem i _ (z i))
      (fun i => restrictMem i _ (s i)) 2 (2*errorConstant) (accepted_score n grow hn ho)
      (accepted_score_limit n grow hn ho)
    intro i
    have sw := stopped_bounds (n i) (S (n i))
    have h := accepted_transfer (n i) (S (n i)) (hn i) (ho i) (common_cap (n i)) _ sw.1 sw.2
    have f := denominator_floor (n i) (hn i)
    apply h.trans
    have x := div_le_div₀ ((sqrt_nonneg _).trans (cerr i)) (cerr i) (by norm_num : (0:ℝ)<1/2) f
    exact x.trans_eq (by ring)

theorem actual_short_theta (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    ((fun i => rms (seedLaw (Width (n i))) (fixed (n i) (S (n i)))) =Θ[atTop] (fun i => scale (n i))) ∧
    ((fun i => rms (seedLaw (Width (n i))) (capped (n i) (S (n i)))) =Θ[atTop] (fun i => scale (n i))) ∧
    ((fun i => rms (acceptedLaw (n i)) (fixed (n i) (S (n i)))) =Θ[atTop] (fun i => scale (n i))) := by
  have h := actual_short_results n grow hn ho
  exact ⟨h.1.1,h.2.1.1,h.2.2.1⟩

/-- The three RMS statistics are asymptotically equivalent to the identical
finite-grid formula. It retains the coefficient, actual kernel eigenvalue,
integer early cap and finite-width Gaussian seed-score norm. -/
theorem actual_short_equivalent (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (ho : ∀ i, Odd (n i+1)) :
    ((fun i => rms (seedLaw (Width (n i))) (fixed (n i) (S (n i)))) ~[atTop] (fun i => leading (n i))) ∧
    ((fun i => rms (seedLaw (Width (n i))) (capped (n i) (S (n i)))) ~[atTop] (fun i => leading (n i))) ∧
    ((fun i => rms (acceptedLaw (n i)) (fixed (n i) (S (n i)))) ~[atTop] (fun i => leading (n i))) := by
  have h := actual_short_results n grow hn ho
  exact ⟨h.1.2,h.2.1.2,h.2.2.2⟩

end CircleShortEquivalent
