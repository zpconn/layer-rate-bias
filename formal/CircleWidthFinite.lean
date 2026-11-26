module

public import CircleWidthUpper
public import CircleWidthGaussianEnergy
public import CircleWidthPathEnergy
import all CircleEscape
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleCapMoments
import all CircleWidthUpper
import all CircleWidthMoment
import all CircleWidthTracking
import all CircleGaussianTracking
import all CircleShortGDTails
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! Finite layer-cake estimates for the actual unrestricted update. -/
@[expose] public section
noncomputable section
namespace CircleWidthFinite
open Real MeasureTheory ProbabilityTheory Set Filter CircleEscapeBridge CircleWidthUpper
  CircleWidthMoment CircleWidthTracking

/-- Exact truncated second moment from a one-sided tail on a finite interval.
The estimate uses each level separately and does not require nested good events. -/
theorem truncated_square {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (mx : Measurable X) {a D h : ℝ} (ap : 0<a) (d1 : 1≤D) (h1 : 1≤h)
    (tail : ∀ d, 1≤d → d≤D → μ.real {z | a*d< |X z|} ≤ exp (h-d)) :
    ∫ z, (min |X z| (a*D))^2 ∂μ ≤ a^2*(h^2+2*h+2) := by
  let U (z : Ω) := min (|X z|/a) D
  let V (z : Ω) := max 0 (U z-h)
  have d0 : 0≤D := by linarith
  have h0 : 0≤h := by linarith
  have mu : Measurable U := by dsimp [U];fun_prop
  have mv : Measurable V := measurable_const.max (mu.sub_const _)
  have up (z : Ω) : 0≤U z := le_min (div_nonneg (abs_nonneg _) ap.le) d0
  have ud (z : Ω) : U z≤D := min_le_right _ _
  have vp (z : Ω) : 0≤V z := le_max_left _ _
  have vd (z : Ω) : V z≤D := max_le d0 (by linarith [ud z])
  have et (t : ℝ) (tp : 0<t) : μ.real {z | t<V z} ≤ exp (-t) := by
    by_cases l : h+t≤D
    · have sub : {z | t<V z} ⊆ {z | a*(h+t)< |X z|} := by
        intro z hz
        have hh := (lt_max_iff.mp (show t<max 0 (U z-h) from hz)).resolve_left (not_lt.mpr tp.le)
        have ww : h+t< |X z|/a := lt_of_lt_of_le (by linarith : h+t<U z) (min_le_left _ _)
        change a*(h+t)< |X z|
        simpa only [mul_comm] using (lt_div_iff₀ ap).mp ww
      exact (measureReal_mono sub).trans ((tail _ (by linarith) l).trans_eq (by ring_nf))
    · have emp : {z | t<V z} = ∅ := eq_empty_iff_forall_notMem.mpr (fun z hz =>
        (not_lt.mpr (max_le tp.le (by linarith [ud z]) : V z≤t)) hz)
      simp [emp,(exp_pos (-t)).le]
  let F (z : Ω) := 2*h*V z+(V z)^2
  let g (t : ℝ) := 2*h+2*t
  have fpos (z : Ω) : 0≤F z := add_nonneg (by exact mul_nonneg (by positivity) (vp z)) (sq_nonneg _)
  have prim (v : ℝ) : (∫ t in 0..v, g t) = 2*h*v+v^2 := by
    dsimp [g]
    rw [intervalIntegral.integral_add (f:=fun _ : ℝ => 2*h) (g:=fun t : ℝ => 2*t) (continuous_const.intervalIntegrable ..) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
    simp only [sub_zero,smul_eq_mul]
    ring
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ (f:=V) (g:=g) (ae_of_all _ vp)
    mv.aemeasurable (fun _ _ => Continuous.intervalIntegrable (by dsimp [g];fun_prop) _ _)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => by dsimp [g];linarith [mem_Ioi.mp ht]))
  simp_rw [prim] at key
  have gram : (∫ t : ℝ in Ioi 0, t*exp (-t))=1 := by
    have eq := integral_rpow_mul_exp_neg_mul_Ioi (a:=2) (r:=1) (by norm_num) (by norm_num)
    norm_num [show (2:ℝ)=1+1 by norm_num,Gamma_add_one, Gamma_one] at eq
    exact eq
  have ie : IntegrableOn (fun t : ℝ => exp (-t)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [integral_exp_neg_Ioi_zero];norm_num)
  have it : IntegrableOn (fun t : ℝ => t*exp (-t)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [gram];norm_num)
  have eqg : (fun t : ℝ => exp (-t)*g t) = fun t => (2*h)*exp (-t)+2*(t*exp (-t)) := by
    funext t;dsimp [g];ring
  have ig : IntegrableOn (fun t : ℝ => exp (-t)*g t) (Ioi 0) := by
    rw [eqg];exact (ie.const_mul _).add (it.const_mul _)
  have val : (∫ t : ℝ in Ioi 0, exp (-t)*g t)=2*h+2 := by
    rw [eqg,integral_add (ie.const_mul _) (it.const_mul _),integral_const_mul,integral_const_mul,
      gram,integral_exp_neg_Ioi_zero];ring
  have bound : ∫ z, F z ∂μ ≤ 2*h+2 := by
    rw [← val,integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fpos) (by dsimp [F];fun_prop)]
    rw [integral_eq_lintegral_of_nonneg_ae ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht =>
      mul_nonneg (exp_pos _).le (by dsimp [g];linarith [mem_Ioi.mp ht]))) ig.aestronglyMeasurable]
    apply ENNReal.toReal_mono (ig.lintegral_lt_top.ne)
    change (∫⁻ z, ENNReal.ofReal (2*h*V z+(V z)^2) ∂μ) ≤ _
    rw [key]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    rw [ENNReal.ofReal_mul (exp_pos _).le]
    apply mul_le_mul_left
    simpa [measureReal_def] using ENNReal.ofReal_le_ofReal (et t ht)
  have fi : Integrable F μ := by
    apply (integrable_const (2*h*D+D^2)).mono' (by dsimp [F];fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (fpos z)]
    exact add_le_add (mul_le_mul_of_nonneg_left (vd z) (by positivity)) (pow_le_pow_left₀ (vp z) (vd z) 2)
  have ui : Integrable (fun z => (U z)^2) μ := (integrable_const (D^2)).mono' (by fun_prop)
    (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (up z) (ud z) 2))
  have ubd : (∫ z, (U z)^2 ∂μ) ≤ h^2+2*h+2 := by
    have le := integral_mono ui ((integrable_const (h^2)).add fi) (fun z => show (U z)^2≤h^2+F z by
      have hv : U z≤h+V z := by linarith [le_max_right 0 (U z-h)]
      have sq := pow_le_pow_left₀ (up z) hv 2
      dsimp [F];nlinarith)
    simp only [Pi.add_apply,integral_add (integrable_const (h^2)) fi,integral_const,
      probReal_univ,one_smul] at le
    linarith
  convert (mul_le_mul_of_nonneg_left ubd (sq_nonneg a)) using 1
  rw [← integral_const_mul]
  congr 1
  funext z
  have eq : a*U z=min |X z| (a*D) := by dsimp only [U];rw [mul_min_of_nonneg _ _ ap.le,mul_div_cancel₀ _ ap.ne']
  rw [← eq,mul_pow]

/-- The fourth root of the terminal failure mass enters the root-MSE even
when the events from the finite tail bounds cannot be chosen jointly. -/
theorem finite_rms {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (mx : Measurable X) (m4 : MemLp X 4 μ) {a D h K : ℝ}
    (ap : 0<a) (d1 : 1≤D) (h1 : 1≤h) (kp : 0≤K)
    (tail : ∀ d, 1≤d → d≤D → μ.real {z | a*d< |X z|} ≤ exp (h-d))
    (four : ∫ z, X z^4 ∂μ ≤ K^4) :
    sqrt (∫ z, X z^2 ∂μ) ≤ a*sqrt (h^2+2*h+2)+K*sqrt (sqrt (min 1 (exp (h-D)))) := by
  let E := {z | a*D< |X z|}
  let V (z : Ω) := min |X z| (a*D)
  have d0 : 0≤D := by linarith
  have vp (z : Ω) : 0≤V z := le_min (abs_nonneg _) (mul_nonneg ap.le d0)
  have me : MeasurableSet E := measurableSet_lt measurable_const (continuous_abs.measurable.comp mx)
  have mv : Measurable V := by dsimp [V];fun_prop
  have hi := (m4.mono_exponent (by norm_num : (2:ENNReal)≤4)).integrable_sq
  have iv : Integrable (fun z => V z^2) μ := (integrable_const ((a*D)^2)).mono' (mv.pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (vp z) (min_le_right _ _) 2))
  have mono := integral_mono hi (iv.add (hi.indicator me)) (fun z => show X z^2 ≤ V z^2+E.indicator (fun z => X z^2) z by
    by_cases e : z∈E
    · rw [indicator_of_mem e];linarith [sq_nonneg (V z)]
    · rw [indicator_of_notMem e,add_zero];dsimp [V];rw [min_eq_left (le_of_not_gt e),sq_abs])
  change (∫ z, X z^2 ∂μ) ≤ ∫ z, V z^2+E.indicator (fun z => X z^2) z ∂μ at mono
  rw [integral_add iv (hi.indicator me),integral_indicator me] at mono
  have trunc := truncated_square mx ap d1 h1 tail
  have hold := CircleMoment.exceptional_second_moment (CircleGaussianTracking.square_mem m4) E
  have pe : μ.real E≤min 1 (exp (h-D)) := le_min measureReal_le_one (tail D d1 le_rfl)
  have pos : 0≤min 1 (exp (h-D)) := le_min zero_le_one (exp_nonneg _)
  have k2 : sqrt (∫ z, X z^4 ∂μ) ≤ K^2 :=
    (sqrt_le_sqrt four).trans_eq (by rw [show K^4=(K^2)^2 by ring,sqrt_sq (sq_nonneg _)])
  have coef : 0≤h^2+2*h+2 := by nlinarith [sq_nonneg h]
  have p := (mono.trans (add_le_add (b:=a^2*(h^2+2*h+2)) trunc (hold.trans
    (mul_le_mul k2 (sqrt_le_sqrt pe) (sqrt_nonneg _) (sq_nonneg _)))))
  apply (sqrt_le_iff.mpr ⟨by positivity,?_⟩)
  apply p.trans
  rw [add_sq,mul_pow,mul_pow,sq_sqrt coef,sq_sqrt (sqrt_nonneg _)]
  linarith only [mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) (mul_nonneg ap.le (sqrt_nonneg (h^2+2*h+2))))
    (mul_nonneg kp (sqrt_nonneg (sqrt (min 1 (exp (h-D))))))]

def level (m T : ℕ) : ℝ := m/(400000^2*(1+(T:ℝ))^4)
def slope (m T : ℕ) : ℝ := 220000000*(1+(T:ℝ))^2/sqrt m
def logCount (N : ℕ) : ℝ := log (8*((N:ℝ)+1)^2)

theorem actual_tail {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η : ℝ} (hη : 0≤η) (hc : η≤1) {d : ℝ} (d1 : 1≤d) (dc : d≤level m T) :
    (seedLaw m).real {z | slope m T*d< |rawError (n+1) m T η (stoppedCoefficient n T η) z|} ≤
      exp (logCount (n+1)-d) := by
  let w : ℝ := 1+T
  let q := sqrt d/sqrt m
  let u := 192*q
  let ρ := 3104*T*q
  have wp : 0<w := by dsimp [w];positivity
  have w1 : 1≤w := by dsimp [w];linarith [Nat.cast_nonneg (α:=ℝ) T]
  have tw : (T:ℝ)≤w := by dsimp [w];linarith
  have mp : 0<sqrt (m:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have d0 : 0≤d := by linarith
  have su : 1≤sqrt d := one_le_sqrt.mpr d1
  have qp : 0≤q := div_nonneg (sqrt_nonneg d) mp.le
  have qq : q*(400000*w^2)≤1 := by
    have di : d*(400000^2*w^4)≤m := (le_div_iff₀ (by positivity)).mp dc
    have rt := sqrt_le_sqrt di
    have eq : sqrt (d*(400000^2*w^4))=sqrt d*(400000*w^2) := by
      rw [sqrt_mul d0,show (400000:ℝ)^2*w^4=(400000*w^2)^2 by ring,sqrt_sq (by positivity)]
    rw [eq] at rt
    dsimp [q];rw [div_mul_eq_mul_div,div_le_one mp];exact rt
  have wu : 0≤u := by dsimp [u];positivity
  have r0 : 0≤ρ := by dsimp [ρ];positivity
  have two : 1≤w^2 := one_le_pow₀ w1
  have q1 : 400000*q≤1 := by nlinarith only [qq,mul_le_mul_of_nonneg_left two qp]
  have t2 : (T:ℝ)≤w^2 := tw.trans ((by simpa using (pow_le_pow_right₀ w1 (by decide : 1≤2))))
  have r1 : ρ≤1 := by dsimp [ρ];nlinarith only [qq,mul_le_mul_of_nonneg_right t2 qp,qp]
  have u1 : u≤1 := by dsimp [u];linarith
  have rle : 2+sqrt m*u ≤ 194*sqrt d := by
    dsimp [u,q];field_simp; nlinarith only [su]
  have ee : 2*(30*ρ+3*u)≤187392*w*q := by
    dsimp [ρ,u,w];nlinarith only [qp,Nat.cast_nonneg (α:=ℝ) T]
  have ww : (T:ℝ)*w≤w^2 := by nlinarith only [mul_le_mul_of_nonneg_right tw wp.le]
  have hr : FitsBudget m T ρ u := by
    refine ⟨r0,r1,wu,u1,?_,?_⟩
    · have r := mul_le_mul_of_nonneg_left rle (show 0≤16/sqrt (m:ℝ) by positivity)
      dsimp [ρ,q]
      calc _ ≤ T*(16/sqrt m*(194*sqrt d)) := mul_le_mul_of_nonneg_left r (Nat.cast_nonneg T)
           _ = _ := by ring
    · nlinarith only [qq,mul_le_mul_of_nonneg_left ee (Nat.cast_nonneg T),mul_le_mul_of_nonneg_right ww qp,qp,mul_nonneg (sq_nonneg w) qp]
  have err : errorBound m T ρ u ≤ slope m T*d := by
    have p := mul_le_mul ee rle (by positivity : 0≤2+sqrt m*u) (by positivity : 0≤187392*w*q)
    have qd : q*sqrt d=d/sqrt m := by dsimp [q];rw [div_mul_eq_mul_div,← sq,sq_sqrt d0]
    have compat : 187392*w*q*(194*sqrt d) = (187392*194)*w*(d/sqrt m) := by rw [←qd];ring
    rw [compat] at p
    unfold errorBound slope
    have W := mul_le_mul_of_nonneg_right ww (div_nonneg d0 mp.le)
    change _ ≤ 220000000*w^2/sqrt m*d
    nlinarith only [mul_le_mul_of_nonneg_right p (Nat.cast_nonneg T),W,mul_nonneg (sq_nonneg w) (div_nonneg d0 mp.le),
      show 220000000*w^2/sqrt m*d=220000000*(w^2*(d/sqrt m)) by ring]
  have sub : {z | slope m T*d< |rawError (n+1) m T η (stoppedCoefficient n T η) z|} ⊆ exceptional (n+1) m ρ u := by
    intro z hz
    by_contra h
    exact (not_lt.mpr ((CircleWidthUpper.inside hn odd hm hη hc hr z h).trans err)) hz
  apply (measureReal_mono sub).trans ((probability (N:=n+1) hm r0 r1 wu u1).trans_eq ?_)
  have eq : (m:ℝ)*u^2/36864=d := by
    dsimp [u,q];rw [mul_pow,div_pow,sq_sqrt d0,sq_sqrt (Nat.cast_nonneg m)];field_simp;ring
  rw [logCount,exp_sub,exp_log (by positivity),failureBound,neg_mul,neg_div,eq,exp_neg,div_eq_mul_inv]


/-- The published fourth moment constant for the unrestricted, trained network,
including all exceptional Gaussian seeds. -/
theorem actual_fourth {N m T : ℕ} (hn : 0<N) (hm : 0<m) (width : 4*3^T≤m)
    {η b : ℝ} (hη : 0≤η) (hc : η≤1) (hb : 0≤b) (h1 : b≤1) :
    ∫ ω, rawError N m T η b ω^4 ∂seedLaw m ≤ (2*sqrt m*14^(3^T))^4 := by
  let S (ω : Seed m) := 4+2*CircleCapInduction.energy (initial ω)
  have p4 : MemLp (rawError N m T η b) (4:ℕ) (seedLaw m) := raw_mem4 _ _ _ _ _
  have ix : Integrable (fun ω => rawError N m T η b ω^4) (seedLaw m) := by
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using p4.integrable_norm_pow'
  have hs := CircleWidthGaussianEnergy.initial_energy_power_integrable m _ width
  have h := integral_mono ix (hs.const_mul ((2*sqrt (m:ℝ))^4)) (fun ω => by
    have q := pow_le_pow_left₀ (abs_nonneg _) (CircleWidthPathEnergy.actual_paired hη hc hn hm hb h1 T ω) 4
    simpa only [(by decide : Even 4).pow_abs,mul_pow,←pow_mul,Nat.mul_comm 4] using q)
  change _ ≤ ∫ ω, (2*sqrt (m:ℝ))^4*S ω^(4*3^T) ∂seedLaw m at h
  rw [integral_const_mul] at h
  apply (h.trans (mul_le_mul_of_nonneg_left (CircleWidthGaussianEnergy.initial_energy_power m _ width) (by positivity))).trans_eq
  rw [mul_pow (2*sqrt (m:ℝ)),←pow_mul,Nat.mul_comm 4]

private theorem stopped_bounds (n T : ℕ) {η : ℝ} (hη : 0≤η) (hc : η≤1) :
    0≤stoppedCoefficient n T η ∧ stoppedCoefficient n T η≤1 := by
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have gp : 0≤CircleKernelGD.gamma (n+1) := (show 0≤(3:ℝ)/π^2 by positivity).trans CircleKernelGD.gamma_bounds.1
  have al : 0≤1-η*CircleKernelGD.gamma (n+1) := sub_nonneg.mpr ((mul_le_of_le_one_left gp hc).trans CircleKernelGD.gamma_bounds.2)
  have a1 : 1-η*CircleKernelGD.gamma (n+1)≤1 := sub_le_self _ (mul_nonneg hη gp)
  exact ⟨mul_nonneg wb.1 (sub_nonneg.mpr (pow_le_one₀ al a1)),
    (mul_le_of_le_one_right wb.1 (sub_le_self _ (pow_nonneg al T))).trans wb.2⟩

private theorem error_meas (N m T : ℕ) (η b : ℝ) : Measurable (rawError N m T η b) := by
  apply Measurable.sub _ (CircleCapMoments.reference_measurable N m b)
  unfold trainedMean CircleEscape.populationMean
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ fun j _ =>
    (CircleSeedIntegrability.parameter_measurable N m η T j).1.mul (CircleSeedIntegrability.parameter_measurable N m η T j).2.norm

private theorem logCount_ge_one (N : ℕ) : 1≤logCount N := by
  apply (le_log_iff_exp_le (by positivity)).mpr
  have one : (1:ℝ)≤((N:ℝ)+1)^2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  linarith [Real.exp_one_lt_d9]

/-- Fully instantiated finite-width estimate using the general two-rate concentration
and path inequalities specialized to rate one. -/
theorem conservative_finite {n m T : ℕ} (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    (width : 4*3^T≤m) (level_ge : 1≤level m T) {η : ℝ} (hη : 0≤η) (hc : η≤1) :
    let h := logCount (n+1)
    sqrt (∫ z, (rawError (n+1) m T η (stoppedCoefficient n T η) z)^2 ∂seedLaw m) ≤
      slope m T*sqrt (h^2+2*h+2)+2*sqrt m*14^(3^T)*sqrt (sqrt (min 1 (exp (h-level m T)))) := by
  intro h
  have b := stopped_bounds n T hη hc
  exact finite_rms (error_meas ..) (raw_mem4 ..) (by unfold slope;positivity) level_ge (logCount_ge_one _) (by positivity)
    (fun _ lo hi => actual_tail hn odd hm hη hc lo hi) (actual_fourth (by omega) hm width hη hc b.1 b.2)
end CircleWidthFinite
