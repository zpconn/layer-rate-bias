module

public import CircleWidthEnergyScreen
import all CircleWidthThreshold
import all CircleWidthEnergyScreen
import all CircleWidthMoment
import all CircleKernelGD
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleGaussianTracking
public import CircleComparison
import Mathlib.Tactic

/-! A polynomial correction to the sufficient exponential width at long caps. -/
@[expose] public section
noncomputable section
namespace CircleWidthPolynomial
open Real Filter Set MeasureTheory CircleWidthUpper CircleWidthThreshold CircleWidthEnergyScreen
  CircleWidthTracking CircleWidthMoment CircleWidthAsymptotics
open scoped Topology

/-- At least 10⁸ T 3ᵀ parameters suffice for superpolynomial paired accuracy
on a growing grid with log N=o(T). -/
theorem polynomial_window (n m T : ℕ → ℕ) (η : ℕ → ℝ)
    (grow : Tendsto T atTop atTop)
    (valid : ∀ᶠ j in atTop, 81≤n j+1 ∧ Odd (n j+1) ∧ 0<m j ∧ 0≤η j ∧ η j≤1)
    (grid : Tendsto (fun j => log ((n j:ℝ)+1)/(T j:ℝ)) atTop (𝓝 0))
    (width : ∀ᶠ j in atTop, 100000000*(T j:ℝ)*(3:ℝ)^(T j)≤m j) (k : ℝ) :
    Tendsto (fun j => ((n j:ℝ)+1)^k * ∫ z, (rawError (n j+1) (m j) (T j) (η j)
      (stoppedCoefficient (n j) (T j) (η j)) z)^2 ∂CircleEscapeBridge.seedLaw (m j)) atTop (𝓝 0) := by
  let x := fun j => log (m j)
  let l := log 3
  have lp : 0<l := log_pos (by norm_num)
  have lu : l≤2 := (log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)).trans_eq (by norm_num)
  have tg := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have t1 : ∀ᶠ j in atTop, (1:ℝ)≤T j := tg.eventually_ge_atTop 1
  have ratio : ∀ᶠ j in atTop, l*(T j:ℝ)≤x j := by
    filter_upwards [width,t1] with j w t
    have pp : 0<(3:ℝ)^(T j) := by positivity
    have h : (3:ℝ)^(T j)≤m j := by nlinarith only [w,mul_le_mul_of_nonneg_right t pp.le,pp]
    simpa [x,l,log_pow,mul_comm] using log_le_log pp h
  have xg : Tendsto x atTop atTop := tendsto_atTop_mono' atTop ratio (tg.const_mul_atTop lp)
  have tx : ∀ᶠ j in atTop, (T j:ℝ)≤x j/l := ratio.mono fun j h => (le_div_iff₀ lp).mpr (by linarith)
  have sm (v : ℝ) (vp : 0<v) (C : ℝ) :
      Tendsto (fun j => C*x j*exp (-v*x j)) atTop (𝓝 0) := by
    simpa [mul_assoc,Function.comp_def] using ((linear_times_decay vp).comp xg).const_mul C
  have sm' (v : ℝ) (vp : 0<v) (C : ℝ) :
      ∀ᶠ j in atTop, C*x j≤exp (v*x j) := by
    filter_upwards [(sm v vp C).eventually_le_const (by norm_num : (0:ℝ)<1)] with j h
    rw [neg_mul,exp_neg,←div_eq_mul_inv] at h
    simpa using (div_le_iff₀ (exp_pos _)).mp h
  have slow (C : ℝ) : ∀ᶠ j in atTop, C*log ((n j:ℝ)+1)≤x j := by
    have h0 := grid.const_mul C
    have e := h0.eventually_le_const (by simpa using lp : C*0<l)
    filter_upwards [e,ratio,t1] with j h h' t
    change C*(log ((n j:ℝ)+1)/(T j:ℝ))≤l at h
    rw [←mul_div_assoc] at h
    exact ((div_le_iff₀ (by linarith only [t] : 0<(T j:ℝ))).mp h).trans h'
  have cost : ∀ᶠ j in atTop, 160*x j*(3:ℝ)^(T j)≤(m j:ℝ)/100000 := by
    filter_upwards [valid,width,sm' (1/2) (by norm_num) 16000000] with j v w small
    have mx : (m j:ℝ)=exp (x j) := (exp_log (Nat.cast_pos.mpr v.2.2.1)).symm
    by_cases h : l*(T j:ℝ)≤x j/2
    · have p : (3:ℝ)^(T j)≤exp ((1/2)*x j) := by
        rw [← exp_log (pow_pos (by norm_num : (0:ℝ)<3) (T j)),log_pow]
        exact exp_le_exp.mpr (by dsimp only [l] at h; linarith)
      have hl := mul_le_mul small p (by positivity) (exp_nonneg _)
      rw [←exp_add,show 1/2*x j+1/2*x j=x j by ring,←mx] at hl
      linarith
    · have xp : x j≤4*(T j:ℝ) := by nlinarith only [h,mul_le_mul_of_nonneg_right lu (Nat.cast_nonneg (T j))]
      nlinarith only [w,mul_le_mul_of_nonneg_right xp (pow_nonneg (by norm_num : (0:ℝ)≤3) (T j)),
        mul_nonneg (Nat.cast_nonneg (T j)) (pow_nonneg (by norm_num : (0:ℝ)≤3) (T j))]
  have van := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (xg.const_mul_atTop (by norm_num : (0:ℝ)<1/32))).const_mul 3
  simp only [mul_zero] at van
  apply squeeze_zero' (Eventually.of_forall fun j => mul_nonneg (rpow_nonneg (by positivity) _) (integral_nonneg fun _ => sq_nonneg _)) _ van
  filter_upwards [valid,width,t1,ratio,tx,xg.eventually_ge_atTop 64,slow 1,slow (32*k),cost,
    sm' (3/16) (by norm_num) (132/l),sm' (1/32) (by norm_num) (1188/l),
    sm' (1/4) (by norm_num) (9*36864),sm' 1 (by norm_num) (8*100000)] with j v w t rat tj x1 g gk co rd ed mid tail
  have mx : (m j:ℝ)=exp (x j) := (exp_log (Nat.cast_pos.mpr v.2.2.1)).symm
  have xp : 0<x j := by linarith
  have nn : ((n j+1:ℕ):ℝ)≤exp (1*x j) := by
    rw [one_mul,Nat.cast_add_one,←log_le_iff_le_exp (by positivity)]; linarith
  have span : 12*T j≤m j := by
    have h := one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=T j)
    exact_mod_cast (show 12*(T j:ℝ)≤m j by nlinarith only [w,mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (T j)),t])
  have budget : 132*(T j:ℝ)*CircleWidthThreshold.r (3/8) (x j)≤1 := by
    rw [CircleWidthThreshold.r,neg_mul,exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (exp_pos _)).mpr
    convert (mul_le_mul_of_nonneg_left tj (by norm_num : (0:ℝ)≤132)).trans ((by ring : 132*(x j/l)=132/l*x j) ▸ rd) using 2; ring
  have sc := CircleWidthThreshold.scales (m j) (T j) (3/8) _ mx xp.le (by norm_num) (by norm_num) budget
  have b := screened_mse (n j) (m j) (T j) v.1 v.2.1 v.2.2.1 span v.2.2.2.1 v.2.2.2.2 sc.1
  have front : (errorBound (m j) (T j) (CircleWidthThreshold.r (3/8) (x j)) (CircleWidthThreshold.u (3/8) (x j)))^2 ≤ exp (-(x j/16)) := by
    have hh := sc.2
    norm_num at hh
    have cap : 1188*(T j:ℝ)≤exp (1/32*x j) :=
      (mul_le_mul_of_nonneg_left tj (by norm_num : (0:ℝ)≤1188)).trans ((by ring : 1188*(x j/l)=1188/l*x j) ▸ ed)
    have h := hh.trans (mul_le_mul_of_nonneg_right cap (exp_nonneg _))
    rw [←exp_add] at h
    apply (pow_le_pow_left₀ (by unfold errorBound CircleWidthThreshold.r CircleWidthThreshold.u;positivity) h 2).trans_eq
    rw [←exp_nat_mul];congr 1;ring
  have middle : 64*(m j:ℝ)*failureBound (n j+1) (m j) (CircleWidthThreshold.u (3/8) (x j))≤exp (-(x j/16)) := by
    have p := CircleWidthThreshold.failure_exp (n j+1) (m j) (3/8) (x j) 1 mx nn (by linarith) (by linarith)
    have big : 64≤exp (x j) := by linarith [Real.add_one_le_exp (x j)]
    apply (mul_le_mul_of_nonneg_left p (by positivity : (0:ℝ)≤64*m j)).trans
    rw [mx]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right big (exp_nonneg _)) (exp_nonneg _)).trans
    rw [←exp_add,←exp_add]
    apply exp_le_exp.mpr
    norm_num
    linarith only [mid,xp.le]
  have rare : sqrt (CircleShortGDTails.fourthBound (m j) (T j))*sqrt (failureBound (n j+1) (m j) 1)≤ exp (-(x j/16)) := by
    let β := l*(T j:ℝ)/x j
    have be : β*x j=l*(T j:ℝ) := by dsimp [β];field_simp
    have cc : β≤1 := (div_le_one xp).mpr rat
    have bp : 0≤β := by dsimp [β];positivity
    have pe : exp (β*x j)=(3:ℝ)^(T j) := by rw [be,mul_comm,exp_nat_mul,exp_log (by norm_num : 0<(3:ℝ))]
    have f := CircleWidthThreshold.fourth_exp (m j) (T j) β (x j) mx (by linarith) bp cc pe.symm.le
    have p := CircleWidthThreshold.failure_exp (n j+1) (m j) 0 (x j) 1 mx nn (by linarith) (by linarith)
    rw [pe] at f
    simp only [CircleWidthThreshold.u,neg_zero,zero_mul,exp_zero,mul_zero,sub_zero,one_mul,←mx] at p
    rw [← sqrt_mul (by unfold CircleShortGDTails.fourthBound;positivity)]
    apply (sqrt_le_iff).mpr ⟨(exp_pos _).le,?_⟩
    apply (mul_le_mul f p (by unfold failureBound;positivity) (exp_nonneg _)).trans
    rw [←exp_add,←exp_nat_mul]
    apply exp_le_exp.mpr
    rw [one_mul,←mx] at tail
    norm_num
    linarith only [co,tail,xp.le]
  have M := b.trans (add_le_add (add_le_add front middle) rare)
  have nk : ((n j:ℝ)+1)^k≤exp (x j/32) := by
    rw [rpow_def_of_pos (by positivity)];apply exp_le_exp.mpr;linarith only [gk]
  have pos : 0≤∫ z, (rawError (n j+1) (m j) (T j) (η j) (stoppedCoefficient (n j) (T j) (η j)) z)^2 ∂CircleEscapeBridge.seedLaw (m j) :=
    integral_nonneg fun _ => sq_nonneg _
  apply (mul_le_mul nk M pos (exp_nonneg _)).trans_eq
  change exp (x j/32)*(exp (-(x j/16))+exp (-(x j/16))+exp (-(x j/16)))=3*exp (-(1/32*x j))
  rw [show exp (x j/32)*(exp (-(x j/16))+exp (-(x j/16))+exp (-(x j/16)))=
    3*(exp (x j/32)*exp (-(x j/16))) by ring,←exp_add]
  congr 2;ring

/-- The paper's sufficient numerical width implies the stronger linear-in-time
width criterion once the cap grows. -/
theorem published_width (m T : ℕ → ℕ)
    (width : ∀ᶠ j in atTop, 32*1200^2*(1+(T j:ℝ))^4*(3:ℝ)^(T j)≤m j) :
    ∀ᶠ j in atTop, 100000000*(T j:ℝ)*(3:ℝ)^(T j)≤m j := by
  filter_upwards [width] with j w
  apply le_trans _ w
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg ((T j:ℝ)^2),sq_nonneg (T j:ℝ),pow_nonneg (Nat.cast_nonneg (T j) (α:=ℝ)) 3,Nat.cast_nonneg (T j) (α:=ℝ)]

open CircleEscapeBridge CircleSeedIntegrability CircleSpectrum CircleGaussianTracking

theorem coefficient_lag (n T : ℕ → ℕ) (η : ℕ → ℝ) (grow : Tendsto T atTop atTop)
    {η₀ : ℝ} (hp : 0<η₀) (steps : ∀ᶠ j in atTop, η₀≤η j ∧ η j≤1)
    (grid : Tendsto (fun j => log ((n j:ℝ)+1)/(T j:ℝ)) atTop (𝓝 0)) (k : ℝ) :
    Tendsto (fun j => ((n j:ℝ)+1)^k * |stoppedCoefficient (n j) (T j) (η j)-weight 1 (n j)|) atTop (𝓝 0) := by
  let d := η₀*(3/π^2)
  have dp : 0<d := by dsimp [d];positivity
  have tg := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have dec := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tg.const_mul_atTop (half_pos dp))
  apply squeeze_zero' (Eventually.of_forall fun j => mul_nonneg (rpow_nonneg (by positivity) _) (abs_nonneg _)) _ dec
  have small := (grid.const_mul k).eventually_le_const (show k*0<d/2 by linarith)
  filter_upwards [steps,small,tg.eventually_ge_atTop 1] with j ηj sm tj
  have sx : k*log ((n j:ℝ)+1)≤d/2*(T j:ℝ) := by
    change k*(log ((n j:ℝ)+1)/(T j:ℝ))≤d/2 at sm
    change 1≤(T j:ℝ) at tj
    rw [←mul_div_assoc] at sm; exact (div_le_iff₀ (by linarith)).mp sm
  have wb := CircleGaussianTracking.weight_bounds (n j) (by norm_num : 0≤(1:ℝ))
  have gb := CircleKernelGD.gamma_bounds (N:=n j+1)
  have gp := (by positivity : 0≤(3:ℝ)/π^2).trans gb.1
  have lo : d≤η j*CircleKernelGD.gamma (n j+1) := mul_le_mul ηj.1 gb.1 (by positivity) (hp.le.trans ηj.1)
  have hi : η j*CircleKernelGD.gamma (n j+1)≤1 := (mul_le_of_le_one_left gp ηj.2).trans gb.2
  let w := weight 1 (n j)
  let a := 1-η j*CircleKernelGD.gamma (n j+1)
  have ap : 0≤a := sub_nonneg.mpr hi
  have delta : stoppedCoefficient (n j) (T j) (η j)-weight 1 (n j) = -(w*a^(T j)) := by dsimp [stoppedCoefficient,w,a];ring
  have trans := (CircleKernelGD.disc_exp hi (T j)).trans (exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right lo (Nat.cast_nonneg (T j)))))
  rw [delta,abs_neg,abs_of_nonneg (mul_nonneg wb.1 (pow_nonneg ap _))]
  apply (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (pow_nonneg ap _) wb.2).trans trans)
    (rpow_nonneg (by positivity) _)).trans
  rw [rpow_def_of_pos (by positivity),←exp_add]
  apply exp_le_exp.mpr; change _≤ -(d/2*(T j:ℝ)); linarith only [sx]

/-- Superpolynomial paired RMS for the fully fitted kernel reference, still
under the original Gaussian law of the unrestricted fixed-step network. -/
theorem interpolation (n m T : ℕ → ℕ) (η : ℕ → ℝ) (grow : Tendsto T atTop atTop)
    {η₀ : ℝ} (hp : 0<η₀) (valid : ∀ᶠ j in atTop, 81≤n j+1 ∧ Odd (n j+1) ∧ 0<m j ∧ η₀≤η j ∧ η j≤1)
    (grid : Tendsto (fun j => log ((n j:ℝ)+1)/(T j:ℝ)) atTop (𝓝 0))
    (width : ∀ᶠ j in atTop, 100000000*(T j:ℝ)*(3:ℝ)^(T j)≤m j) (k : ℝ) :
    Tendsto (fun j => ((n j:ℝ)+1)^k * sqrt (∫ z, (rawError (n j+1) (m j) (T j) (η j)
      (weight 1 (n j)) z)^2 ∂seedLaw (m j))) atTop (𝓝 0) := by
  let A j := ((n j:ℝ)+1)^k
  let S j := stoppedCoefficient (n j) (T j) (η j)
  let w j := weight 1 (n j)
  let X j := rawError (n j+1) (m j) (T j) (η j) (S j)
  let Y j := rawError (n j+1) (m j) (T j) (η j) (w j)
  let μ j := seedLaw (m j)
  have p := polynomial_window n m T η grow (valid.mono fun j h => ⟨h.1,h.2.1,h.2.2.1,hp.le.trans h.2.2.2.1,h.2.2.2.2⟩) grid width (k+k)
  have sx : Tendsto (fun j => A j * sqrt (∫ z, X j z^2 ∂μ j)) atTop (𝓝 0) := by
    have h := p.sqrt
    rw [sqrt_zero] at h
    apply h.congr
    intro j
    rw [rpow_add (by positivity : 0<((n j:ℝ)+1)),←sq,sqrt_mul (sq_nonneg _),sqrt_sq (rpow_nonneg (by positivity) _)]
  have lag := (coefficient_lag n T η grow hp (valid.mono fun _ h => h.2.2.2) grid k).mul_const CircleResidualSpectrum.modeConstant
  simp only [zero_mul] at lag
  have lim := sx.add lag
  simp only [add_zero] at lim
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (rpow_nonneg (by positivity) _) (sqrt_nonneg _)) _ lim
  filter_upwards [valid] with j v
  let Y₀ := trainedMean (path (n j+1) (m j) (η j)) (T j)
  have norm := CircleComparison.change_reference_bound (by omega : 3≤n j+1) v.2.2.1 Y₀
    (trained_memLp _ _ _ _ 2 (by norm_num)) (w j) (S j)
  apply (mul_le_mul_of_nonneg_left norm (show 0≤A j by dsimp [A];positivity)).trans_eq
  change A j*(sqrt (∫ z, X j z^2 ∂μ j)+ |S j-w j| *CircleResidualSpectrum.modeConstant)=_
  dsimp only [A,S,w];ring

/-- The signed bias and seed variance of ordinary GD at any polynomial-window
design have the same limiting constants as the fully fitted circle kernel. -/
theorem population_limits (n m T : ℕ → ℕ) (η : ℕ → ℝ) (gridGrow : Tendsto n atTop atTop)
    (grow : Tendsto T atTop atTop) {η₀ : ℝ} (hp : 0<η₀)
    (valid : ∀ j, 81≤n j+1 ∧ Odd (n j+1) ∧ 0<m j ∧ η₀≤η j ∧ η j≤1)
    (grid : Tendsto (fun j => log ((n j:ℝ)+1)/(T j:ℝ)) atTop (𝓝 0))
    (width : ∀ᶠ j in atTop, 100000000*(T j:ℝ)*(3:ℝ)^(T j)≤m j) :
    let Y j := trainedMean (path (n j+1) (m j) (η j)) (T j)
    Tendsto (fun j => ((n j:ℝ)+1)^2*((∫ z, Y j z ∂seedLaw (m j))-1)) atTop (𝓝 (-(π^2/36))) ∧
    Tendsto (fun j => ((n j:ℝ)+1)^4*ProbabilityTheory.variance (Y j) (seedLaw (m j))) atTop (𝓝 (7*π^2/1620)) := by
  intro Y
  have p := interpolation n m T η grow hp (Eventually.of_forall valid) grid width 2
  norm_num only [rpow_ofNat] at p
  have v := CircleComparison.gaussian_reference_transfer n m gridGrow (fun j => by have := (valid j).1;omega)
    (fun j => (valid j).2.1) (fun j => (valid j).2.2.1) (τ:=1) (by norm_num) Y
    (fun _ => trained_memLp _ _ _ _ 2 (by norm_num)) p
  constructor
  · convert v.1.neg using 2 with j <;> ring
  · convert v.2 using 2;ring

/-- The paper's explicit full-fit cap grows at least linearly in grid size. -/
theorem grid_le_fitHorizon {N : ℕ} (hn : 1≤N) : N≤CircleCapInduction.fitHorizon N := by
  have n1 : 1≤(N:ℝ) := by exact_mod_cast hn
  have p := one_le_rpow n1 (by norm_num : (0:ℝ)≤7/2)
  have root : 2≤sqrt (12:ℝ) := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have e : exp 1≤ 2*sqrt 12*(N:ℝ)^((7:ℝ)/2) := by
    nlinarith only [mul_le_mul_of_nonneg_left p (by positivity : 0≤2*sqrt (12:ℝ)),root,exp_one_lt_d9.le]
  have logge : 1≤log (2*sqrt 12*(N:ℝ)^((7:ℝ)/2)) := (le_log_iff_exp_le (by positivity)).mpr e
  have nlt : (N:ℝ)≤2*π^2*N^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right (show 1≤2*π^2 by nlinarith [pi_gt_three,sq_nonneg (π-3)]) (sq_nonneg (N:ℝ)),
      mul_le_mul_of_nonneg_right n1 (Nat.cast_nonneg (α:=ℝ) N)]
  apply (Nat.cast_le (α:=ℝ)).mp
  exact nlt.trans ((le_mul_of_one_le_right (by positivity) logge).trans (Nat.le_ceil _))

/-- Numerical bias and variance limits at the prescribed full-fit cap, under
the sufficient width appearing in the paper. -/
theorem fitHorizon_limits (n m : ℕ → ℕ) (η : ℝ) (hη : 0<η) (hc : η≤1) (growth : Tendsto n atTop atTop)
    (valid : ∀ j, 81≤n j+1 ∧ Odd (n j+1) ∧ 0<m j)
    (width : ∀ᶠ j in atTop, let t := CircleCapInduction.fitHorizon (n j+1)
      32*1200^2*(1+(t:ℝ))^4*(3:ℝ)^t≤m j) :
    let Y j := trainedMean (path (n j+1) (m j) η) (CircleCapInduction.fitHorizon (n j+1))
    Tendsto (fun j => ((n j:ℝ)+1)^2*((∫ z, Y j z ∂seedLaw (m j))-1)) atTop (𝓝 (-(π^2/36))) ∧
    Tendsto (fun j => ((n j:ℝ)+1)^4*ProbabilityTheory.variance (Y j) (seedLaw (m j))) atTop (𝓝 (7*π^2/1620)) := by
  let T := fun j => CircleCapInduction.fitHorizon (n j+1)
  have nle (j : ℕ) : n j+1≤T j := grid_le_fitHorizon (Nat.succ_pos _)
  have tg : Tendsto T atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ _).trans (nle j)) growth
  have ng : Tendsto (fun j => (n j:ℝ)+1) atTop atTop := tendsto_atTop_mono (fun j => le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp growth)
  have grid : Tendsto (fun j => log ((n j:ℝ)+1)/(T j:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (g:=fun j => log ((n j:ℝ)+1)/((n j:ℝ)+1)) (fun j => div_nonneg (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) (n j)])) (Nat.cast_nonneg _))
    · intro j
      apply div_le_div_of_nonneg_left (log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) (n j)])) (by positivity)
      exact_mod_cast nle j
    · simpa [Function.comp_def] using ((isLittleO_log_rpow_atTop (r:=1) zero_lt_one).tendsto_div_nhds_zero.comp ng)
  exact population_limits n m T (fun _ => η) growth tg hη (fun j => ⟨(valid j).1,(valid j).2.1,(valid j).2.2,le_rfl,hc⟩)
    grid (published_width _ _ width)

end CircleWidthPolynomial
