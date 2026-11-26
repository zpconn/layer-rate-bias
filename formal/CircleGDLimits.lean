module

public import CircleDiscreteMoments
public import CircleComparison
import all CircleComparison
import all CircleKernelGD
import all CircleEscapeBridge
import all CircleCapMoments
import all CircleDiscreteMoments
import all CircleShortGDTails
import all CircleSeedIntegrability
import all CircleFlowTracking
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-! Bias, seed variance and independent-ensemble limits for the ordinary and
initial-curvature-capped simultaneous gradient updates. -/

@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace CircleGDLimits

open MeasureTheory ProbabilityTheory Filter Real Set
open CircleEscapeBridge CircleSeedIntegrability CircleKernelGD CircleDiscreteMoments
  CircleComparison CircleCapMoments CircleShortGDTails CircleFlowTracking
open scoped Topology

abbrev Width (n : ℕ) := (n+1)^32

def fixed (n t : ℕ) := trainedMean (path (n+1) (Width n) 1) t

def capped (n t : ℕ) := cappedY (n+1) (Width n) t

/-- The signed bias, seed variance and MSE of r independent initializations. -/
def LawLimits (n : ℕ → ℕ) (μ : (i : ℕ) → Measure (Seed (Width (n i)))) (Y : (i : ℕ) → Seed (Width (n i)) → ℝ) : Prop :=
  (Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ z, Y i z ∂μ i)-1))
    atTop (𝓝 (-(π^2/36)))) ∧
  (Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (μ i))
    atTop (𝓝 (7*π^2/1620))) ∧
  ∀ r : ℕ, 0<r → Tendsto (fun i => ((n i:ℝ)+1)^4*
    ∫ z : Fin r → Seed (Width (n i)), ((r:ℝ)⁻¹*(∑ j, Y i (z j))-1)^2
      ∂Measure.pi (fun _ : Fin r => μ i))
    atTop (𝓝 (π^4/1296+7*π^2/(1620*(r:ℝ))))

abbrev BenchmarkLimits (n : ℕ → ℕ) (Y : (i : ℕ) → Seed (Width (n i)) → ℝ) :=
  LawLimits n (fun i => seedLaw (Width (n i))) Y

private theorem stopped_close (n T : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (lo : ∀ i, short ((n i:ℝ)+1) ≤ T i) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*|stoppedWeight (n i) (T i)-CircleSpectrum.weight 1 (n i)|)
      atTop (𝓝 0) := by
  have lim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow
  refine squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (abs_nonneg _)) (g:=fun i => 1/((n i:ℝ)+1)) ?_ lim
  intro i
  have gm := gamma_bounds (N:=n i+1)
  have wn := CircleGaussianTracking.weight_bounds (n i) (τ:=1) (by norm_num)
  have g0 : 0 ≤ gamma (n i+1) := (show (0:ℝ)≤3/π^2 by positivity).trans gm.1
  have f := pow_le_pow_of_le_one (sub_nonneg.mpr gm.2) (sub_le_self _ g0) (lo i)
  have decay : (1-gamma (n i+1))^(T i) ≤ 1/((n i:ℝ)+1)^3 :=
    f.trans (by simpa using (short_transient (N:=n i+1)))
  rw [stoppedWeight,show CircleSpectrum.weight 1 (n i)*(1-(1-gamma (n i+1))^(T i))-
    CircleSpectrum.weight 1 (n i) = -(CircleSpectrum.weight 1 (n i)*(1-gamma (n i+1))^(T i)) by ring,
    abs_neg,abs_of_nonneg (mul_nonneg wn.1 (pow_nonneg (sub_nonneg.mpr gm.2) _))]
  apply (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (pow_nonneg (sub_nonneg.mpr gm.2) _) wn.2).trans decay)
    (sq_nonneg _)).trans_eq
  field_simp

private theorem scaled_rms (n : ℕ → ℕ) (grow : Tendsto n atTop atTop) {E : ℕ → ℝ} {C : ℝ} (hc : 0 ≤ C)
    (he : ∀ i, E i ≤ C/((n i:ℝ)+1)^6) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (E i)) atTop (𝓝 0) := by
  have lim := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow).const_mul (sqrt C)
  refine squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) (g:=fun i => sqrt C*(1/((n i:ℝ)+1))) ?_ (by simpa using lim)
  intro i
  have p : 0<((n i:ℝ)+1) := by positivity
  have h := sqrt_le_sqrt (he i)
  rw [sqrt_div hc,show ((n i:ℝ)+1)^6=(((n i:ℝ)+1)^3)^2 by ring,sqrt_sq (by positivity)] at h
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by field_simp)

private theorem limits_of_mse (n T : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (odd : ∀ i, Odd (n i+1)) (lo : ∀ i, short ((n i:ℝ)+1)≤T i)
    (Y : (i : ℕ) → Seed (Width (n i)) → ℝ) (meas : ∀ i, Measurable (Y i))
    (mem : ∀ i, MemLp (Y i) 2 (seedLaw (Width (n i)))) (C : ℝ) (hc : 0≤C)
    (mse : ∀ i, ∫ z, (Y i z-reference (n i+1) (Width (n i)) (stoppedWeight (n i) (T i)) z)^2
      ∂seedLaw (Width (n i)) ≤ C/((n i:ℝ)+1)^6) : BenchmarkLimits n Y := by
  have b := stopped_reference_transfer n (fun i => Width (n i)) grow hn odd
    (fun i => pow_pos (Nat.succ_pos _) _) (τ:=1) (by norm_num) Y mem
    (fun i => stoppedWeight (n i) (T i)) (stopped_close n T grow lo) (scaled_rms n grow hc mse)
  have bias : Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ z, Y i z ∂seedLaw (Width (n i)))-1))
      atTop (𝓝 (-(π^2/36))) := by convert b.1.neg using 2 with i <;> ring
  have var : Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (seedLaw (Width (n i))))
      atTop (𝓝 (7*π^2/1620)) := by convert b.2 using 2; ring
  refine ⟨bias,var,?_⟩
  intro r hr
  convert (bias.pow 2).add (var.div_const r) using 2 with i
  · rw [product_ensemble r hr (Y i) (mem i) (meas i)]
    ring
  · ring

private theorem fixed_measurable (n t : ℕ) : Measurable (fixed n t) := by
  unfold fixed trainedMean CircleEscape.populationMean
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ fun j _ =>
    (parameter_measurable _ _ 1 t j).1.mul (parameter_measurable _ _ 1 t j).2.norm

/-- Ordinary unconditioned unit-step GD at the early cap S = ceil(π² log N). -/
theorem early_fixed_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1)) :
    BenchmarkLimits n (fun i => fixed (n i) (short ((n i:ℝ)+1))) := by
  apply limits_of_mse n _ grow (fun i => by have := hn i;omega) odd (fun _ => le_rfl) _
    (fun _ => fixed_measurable _ _) (fun i => trained_memLp _ _ _ 1 2 (by norm_num))
    ((198*66*17:ℝ)^2+1044*sqrt 12+1) (by positivity)
  intro i
  have h := early_stopped_mse (n i) (hn i) (odd i)
  have hp : 1≤((n i:ℝ)+1) := by linarith [show (0:ℝ)≤n i by positivity]
  have tr : (∫ z, (fixed (n i) (short ((n i:ℝ)+1)) z-reference (n i+1) (Width (n i))
      (stoppedWeight (n i) (short ((n i:ℝ)+1))) z)^2 ∂seedLaw (Width (n i))) ≤
      ((198*66*17:ℝ)^2+1044*sqrt 12+1)/((n i:ℝ)+1)^10 := by
    simpa only [fixed,Width,earlyCap,short,rawError,Nat.cast_add, Nat.cast_one] using h
  exact tr.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hp (by decide : 6≤10)))


private theorem cap_mem {n t : ℕ} (hn : 12000000≤n+1) (odd : Odd (n+1)) (ht : t≤385*(n+1)^3) :
    MemLp (capped n t) 2 (seedLaw (Width n)) := by
  have hm := cappedY_measurable (n+1) (Width n) t (by omega) odd (pow_pos (Nat.succ_pos _) _)
  have inte := (capped_fourth (n+1) (Width n) t (by omega) odd (pow_pos (Nat.succ_pos _) _) (cap_steps hn ht)).1
  have hsq : MemLp (fun z => (capped n t z)^2) 2 (seedLaw (Width n)) := by
    apply (memLp_two_iff_integrable_sq (hm.pow_const 2).aestronglyMeasurable).2
    simpa only [capped, ← pow_mul, Nat.reduceMul] using inte
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 (hsq.integrable one_le_two)

/-- The once-capped update has the same all-seed constants at every count
between S and 385 N³, including the medium and full benchmark caps. -/
theorem capped_limits (n T : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (lo : ∀ i, short ((n i:ℝ)+1)≤T i) (hi : ∀ i, T i≤385*(n i+1)^3) :
    BenchmarkLimits n (fun i => capped (n i) (T i)) := by
  apply limits_of_mse n T grow (fun i => by have := hn i;omega) odd lo _
    (fun i => cappedY_measurable _ _ _ (by have := hn i;omega) (odd i) (pow_pos (Nat.succ_pos _) _))
    (fun i => cap_mem (hn i) (odd i) (hi i)) ((198*66*385:ℝ)^2+1044*sqrt 13) (by positivity)
  intro i
  simpa only [Nat.cast_add,Nat.cast_one,capped,cappedSq] using
    capped_stopped_mse (n i) (hn i) (odd i) (T i) (hi i)

/-- S, M, and H all lie inside the proved finite tracking window. -/
theorem benchmark_times (n : ℕ) :
    let D := (n:ℝ)+1
    short D≤medium D ∧ medium D≤385*(n+1)^3 ∧ short D≤horizon D ∧ horizon D≤385*(n+1)^3 := by
  intro D
  have h1 : 1≤D := by dsimp [D]; linarith [show (0:ℝ)≤n by positivity]
  have hp : 0<D := lt_of_lt_of_le zero_lt_one h1
  have p4 : π^2 ≤ 16 := by nlinarith [sq_nonneg (4-π),pi_lt_four,pi_pos,mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (show 0≤4+π by positivity)]
  have hlog := log_nonneg h1
  have mid : (medium D:ℝ) ≤ 385*D^3 := by
    have hc := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤60) hlog)).le
    have sq : D ≤ D^3 := by simpa only [pow_one] using pow_le_pow_right₀ h1 (by decide : 1≤3)
    change (medium D:ℝ)≤60*log D+1 at hc
    linarith [log_le_self hp.le]
  have lim : ((385*(n+1)^3:ℕ):ℝ) = 385*D^3 := by push_cast; rfl
  refine ⟨Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right (by linarith : π^2≤60) hlog),?_,?_,?_⟩
  · exact_mod_cast (mid.trans_eq lim.symm)
  · apply Nat.ceil_le_ceil
    have hroot : 1≤sqrt (12*D) := one_le_sqrt.mpr (by linarith)
    have sq : D≤D^3 := by simpa only [pow_one] using pow_le_pow_right₀ h1 (by decide : 1≤3)
    have hscale : D≤2*sqrt (12*D)*D^3 := sq.trans (le_mul_of_one_le_left (by positivity) (by linarith))
    have logscale := log_le_log hp hscale
    have fac : π^2≤2*π^2*D^2 := by
      have d2 : 1≤D^2 := one_le_pow₀ h1
      nlinarith [mul_nonneg (sq_nonneg π) (sub_nonneg.mpr d2),sq_nonneg π]
    exact mul_le_mul fac logscale hlog (by positivity)
  · exact_mod_cast ((CircleGaussianTracking.horizon_le_cubic h1).trans_eq lim.symm)

theorem capped_benchmark_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1)) :
    BenchmarkLimits n (fun i => capped (n i) (short ((n i:ℝ)+1))) ∧
    BenchmarkLimits n (fun i => capped (n i) (medium ((n i:ℝ)+1))) ∧
    BenchmarkLimits n (fun i => capped (n i) (horizon ((n i:ℝ)+1))) := by
  have b (i : ℕ) := benchmark_times (n i)
  exact ⟨capped_limits n _ grow hn odd (fun _ => le_rfl) (fun i => (b i).1.trans (b i).2.1),
    capped_limits n _ grow hn odd (fun i => (b i).1) (fun i => (b i).2.1),
    capped_limits n _ grow hn odd (fun i => (b i).2.2.1) (fun i => (b i).2.2.2)⟩


/-- The ordinary fixed-step learner under the normalized restriction of
the original Gaussian law to the initial curvature screen. -/
def acceptedLaw (n : ℕ) := ProbabilityTheory.cond (seedLaw (Width n)) (screen (n+1) (Width n))

private theorem accept_pos {n : ℕ} (hn : 81≤n+1) (ho : Odd (n+1)) :
    seedLaw (Width n) (screen (n+1) (Width n)) ≠ 0 :=
  (measureReal_ne_zero_iff (by finiteness)).1
    (screen_probability (n+1) (Width n) hn ho (pow_pos (Nat.succ_pos _) _)).2.ne'

private theorem fixed_capped {n t : ℕ} {z : Seed (Width n)} (hz : z ∈ screen (n+1) (Width n)) :
    fixed n t z = capped n t z := by
  unfold fixed capped trainedMean cappedY path rate
  rw [CircleInitializationCheck.trajectory_on_check _ _ _ hz]

private theorem accepted_integral {n t : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (f : ℝ → ℝ) :
    (∫ z, f (fixed n t z) ∂acceptedLaw n) =
      (∫ z in screen (n+1) (Width n), f (capped n t z) ∂seedLaw (Width n))/
        (seedLaw (Width n)).real (screen (n+1) (Width n)) := by
  let μ := seedLaw (Width n)
  let A := screen (n+1) (Width n)
  have eq : (∫ z in A, f (fixed n t z) ∂μ) = ∫ z in A, f (capped n t z) ∂μ :=
    setIntegral_congr_fun (screen_measurable _ _ hn ho (pow_pos (Nat.succ_pos _) _))
      (fun _ hz => congrArg f (fixed_capped hz))
  change (∫ z, f (fixed n t z) ∂(μ A)⁻¹ • μ.restrict A) = _/μ.real A
  rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,eq]
  change (μ.real A)⁻¹*_ = _/μ.real A
  rw [div_eq_inv_mul]

private theorem fourth_arithmetic (x : ℝ) : x^2*(81*105+1)/2 ≤ (1044*x)^2 := by
  nlinarith only [sq_nonneg x]

private theorem centered_arithmetic (x : ℝ) : (x-1)^2 ≤ 2*x^2+2 := by
  nlinarith only [sq_nonneg (x+1)]

private theorem rare_centered {n t : ℕ} (hn : 12000000≤n+1) (ho : Odd (n+1)) (ht : t≤385*(n+1)^3) :
    (∫ z in (screen (n+1) (Width n))ᶜ, (capped n t z-1)^2 ∂seedLaw (Width n)) ≤
      (2*1044*sqrt 13+2)/((n:ℝ)+1)^6 := by
  let N := n+1
  let m := Width n
  let μ := seedLaw m
  let B := (screen N m)ᶜ
  let F := capped n t
  have nh : 12000000≤N := hn
  have np : (0:ℝ)<N := by dsimp [N];positivity
  have n1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have mem := cap_mem hn ho ht
  have meas := cappedY_measurable N m t (by omega) (show Odd N from ho) (pow_pos (Nat.succ_pos _) _)
  have fourth := capped_fourth N m t (by omega) (show Odd N from ho) (pow_pos (Nat.succ_pos _) _) (cap_steps hn ht)
  have msq : MemLp (fun z => F z^2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (meas.pow_const 2).aestronglyMeasurable).2
    simpa only [←pow_mul,Nat.reduceMul] using fourth.1
  have root : sqrt (∫ z, F z^4 ∂μ) ≤ 1044*(m:ℝ) := by
    apply (sqrt_le_left (by positivity)).2
    have ub := fourth.2
    rw [gaussian_eighth] at ub
    exact ub.trans (fourth_arithmetic _)
  have prob : μ.real B ≤ 1/(N:ℝ)^158 := reject_pow N hn ho
  have small : μ.real B ≤ 1/(N:ℝ)^6 := prob.trans (div_le_div_of_nonneg_left zero_le_one
    (by positivity) (pow_le_pow_right₀ n1 (by decide : 6≤158)))
  have rareF : (∫ z in B, F z^2 ∂μ) ≤ 1044*sqrt 13/(N:ℝ)^6 := by
    apply ((CircleMoment.exceptional_second_moment msq B).trans
      (mul_le_mul_of_nonneg_right root (sqrt_nonneg _))).trans
    exact cap_tail_arithmetic (Nat.succ_pos n) (prob.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  have fi : Integrable (fun z => F z^2) μ := mem.integrable_sq
  have ui : Integrable (fun z => (F z-1)^2) μ := (mem.sub (memLp_const 1)).integrable_sq
  have two : Integrable (fun z => 2*F z^2+2) μ := (fi.const_mul 2).add (integrable_const 2)
  have h := setIntegral_mono_ae (s:=B) ui.integrableOn two.integrableOn
    (ae_of_all _ fun z => centered_arithmetic (F z))
  change (∫ z in B, (F z-1)^2 ∂μ) ≤ _ at h
  rw [integral_add (fi.integrableOn.const_mul 2) (integrable_const 2),integral_const_mul,
    setIntegral_const,smul_eq_mul] at h
  have hc : (N:ℝ)=(n:ℝ)+1 := by simp [N]
  change (∫ z in B, (F z-1)^2 ∂μ) ≤ _
  rw [←hc]
  linarith only [h,rareF,small,show (2*1044*sqrt 13+2)/(N:ℝ)^6 =
    2*(1044*sqrt 13/(N:ℝ)^6)+2*(1/(N:ℝ)^6) by ring]

private theorem mean_on_compl {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (mem : MemLp F 2 μ) (B : Set Ω) (mb : MeasurableSet B) :
    |∫ z in B, F z ∂μ| ≤ sqrt (∫ z in B, F z^2 ∂μ) := by
  classical
  let X := B.indicator F
  have h := CircleComparison.mean_transfer (mem.indicator mb.nullMeasurableSet) (memLp_const (0:ℝ) (p:=2) (μ:=μ))
  have sq : (fun z => (X z-(0:ℝ))^2) = B.indicator (fun z => F z^2) := by
    funext z
    by_cases hz : z∈B <;> simp [X,hz]
  change |(∫ z, X z ∂μ)-(∫ _, (0:ℝ) ∂μ)| ≤ sqrt (∫ z, (X z-0)^2 ∂μ) at h
  rw [sq] at h
  simpa only [integral_zero,sub_zero,X,integral_indicator mb] using h

/-- Ordinary unit-step GD, conditional on acceptance before training, has the
same bias, variance and independent-ensemble constants as the all-seed capped learner. -/
theorem accepted_limits (n T : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (lo : ∀ i, short ((n i:ℝ)+1)≤T i) (hi : ∀ i, T i≤385*(n i+1)^3) :
    LawLimits n (fun i => acceptedLaw (n i)) (fun i => fixed (n i) (T i)) := by
  let D (i : ℕ) := (n i:ℝ)+1
  let μ (i : ℕ) := seedLaw (Width (n i))
  let ν (i : ℕ) := acceptedLaw (n i)
  let A (i : ℕ) := screen (n i+1) (Width (n i))
  let p (i : ℕ) := (μ i).real (A i)
  let U (i : ℕ) (z : Seed (Width (n i))) := capped (n i) (T i) z-1
  let Y (i : ℕ) := fixed (n i) (T i)
  let C := 2*1044*sqrt 13+2
  let b := -(π^2/36)
  let v := 7*π^2/1620
  have hn' (i : ℕ) : 81≤n i+1 := by have := hn i;omega
  have ma (i : ℕ) : MeasurableSet (A i) := screen_measurable _ _ (by have := hn i;omega)
    (odd i) (pow_pos (Nat.succ_pos _) _)
  have nz (i : ℕ) : μ i (A i) ≠ 0 := accept_pos (hn' i) (odd i)
  let prob (i : ℕ) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (nz i)
  have ymem (i : ℕ) : MemLp (Y i) 2 (ν i) :=
    ((trained_memLp _ _ _ 1 2 (by norm_num)).restrict (s:=A i)).smul_measure (by simpa using nz i)
  have capmem (i : ℕ) := cap_mem (hn i) (odd i) (hi i)
  have mem (i : ℕ) : MemLp (U i) 2 (μ i) := (capmem i).sub (memLp_const 1)
  have di (i : ℕ) : D i ≠ 0 := by dsimp [D];positivity
  have inv : Tendsto (fun i => 1/D i) atTop (𝓝 0) := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow
  have pl : Tendsto p atTop (𝓝 1) := by
    have q : Tendsto (fun i => (μ i).real (A i)ᶜ) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => measureReal_nonneg) (g:=fun i => (1/D i)^158) ?_ (by simpa using inv.pow 158)
      intro i
      simpa only [μ,A,Width,D,Nat.cast_add,Nat.cast_one,one_div,inv_pow] using reject_pow (n i+1) (hn i) (odd i)
    convert (tendsto_const_nhds (x:=(1:ℝ))).sub q using 2 with i
    · rw [measureReal_compl (ma i),probReal_univ]
      dsimp [p];ring
    · ring
  have hrare (i : ℕ) : (∫ z in (A i)ᶜ, U i z^2 ∂μ i) ≤ C/(D i)^6 :=
    rare_centered (hn i) (odd i) (hi i)
  have e1 : Tendsto (fun i => D i^2*(∫ z in (A i)ᶜ, U i z ∂μ i)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero (fun _ => abs_nonneg _) (g:=fun i => D i^2*sqrt (∫ z in (A i)ᶜ, U i z^2 ∂μ i))
      ?_ (scaled_rms n grow (show 0≤C by dsimp [C];positivity) hrare)
    intro i
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (mean_on_compl _ (mem i) _ (ma i).compl) (sq_nonneg _)
  have e2 : Tendsto (fun i => D i^4*(∫ z in (A i)ᶜ, U i z^2 ∂μ i)) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
      (g:=fun i => C*(1/D i)^2) ?_ (by simpa using (inv.pow 2).const_mul C)
    intro i
    exact (mul_le_mul_of_nonneg_left (hrare i) (by positivity : 0≤D i^4)).trans_eq (by field_simp [di i])
  have lim := capped_limits n T grow hn odd lo hi
  have f1 : Tendsto (fun i => D i^2*∫ z, U i z ∂μ i) atTop (𝓝 b) := by
    convert lim.1 using 2 with i
    rw [integral_sub (capmem i |>.integrable one_le_two) (integrable_const _)]
    simp [D]
  have f2 : Tendsto (fun i => D i^4*∫ z, U i z^2 ∂μ i) atTop (𝓝 (v+b^2)) := by
    convert lim.2.1.add (lim.1.pow 2) using 2 with i
    rw [CircleStats.mse_decomposition (capmem i) 1]
    dsimp [D,μ];ring
  have on1 : Tendsto (fun i => D i^2*∫ z in A i, U i z ∂μ i) atTop (𝓝 b) := by
    convert f1.sub e1 using 2 with i
    · rw [← integral_add_compl (ma i) ((mem i).integrable one_le_two)];ring
    · ring
  have on2 : Tendsto (fun i => D i^4*∫ z in A i, U i z^2 ∂μ i) atTop (𝓝 (v+b^2)) := by
    convert f2.sub e2 using 2 with i
    · rw [← integral_add_compl (ma i) (mem i).integrable_sq];ring
    · ring
  have bias : Tendsto (fun i => D i^2*((∫ z, Y i z ∂ν i)-1)) atTop (𝓝 b) := by
    convert on1.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := accepted_integral (n:=n i) (t:=T i) (by have := hn i;omega) (odd i) (fun y => y-1)
      change (∫ z, Y i z-1 ∂ν i)=(∫ z in A i, U i z ∂μ i)/p i at h
      rw [integral_sub ((ymem i).integrable one_le_two) (integrable_const _),integral_const,probReal_univ,one_smul] at h
      rw [h,Pi.div_apply];ring
    · ring
  have risk : Tendsto (fun i => D i^4*∫ z, (Y i z-1)^2 ∂ν i) atTop (𝓝 (v+b^2)) := by
    convert on2.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := accepted_integral (n:=n i) (t:=T i) (by have := hn i;omega) (odd i) (fun y => (y-1)^2)
      change (∫ z, (Y i z-1)^2 ∂ν i)=(∫ z in A i, U i z^2 ∂μ i)/p i at h
      rw [h,Pi.div_apply];ring
    · ring
  have var : Tendsto (fun i => D i^4*ProbabilityTheory.variance (Y i) (ν i)) atTop (𝓝 v) := by
    convert risk.sub (bias.pow 2) using 2 with i
    · rw [CircleStats.mse_decomposition (ymem i) 1];ring
    · ring
  refine ⟨bias,var,?_⟩
  intro r hr
  convert (bias.pow 2).add (var.div_const r) using 2 with i
  · rw [product_ensemble r hr (Y i) (ymem i) (fixed_measurable _ _)]
    dsimp [D];ring
  · dsimp [b,v];ring

theorem accepted_benchmark_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 12000000≤n i+1) (odd : ∀ i, Odd (n i+1)) :
    LawLimits n (fun i => acceptedLaw (n i)) (fun i => fixed (n i) (short ((n i:ℝ)+1))) ∧
    LawLimits n (fun i => acceptedLaw (n i)) (fun i => fixed (n i) (medium ((n i:ℝ)+1))) ∧
    LawLimits n (fun i => acceptedLaw (n i)) (fun i => fixed (n i) (horizon ((n i:ℝ)+1))) := by
  have d (i : ℕ) := benchmark_times (n i)
  exact ⟨accepted_limits n _ grow hn odd (fun _ => le_rfl) (fun i => (d i).1.trans (d i).2.1),
    accepted_limits n _ grow hn odd (fun i => (d i).1) (fun i => (d i).2.1),
    accepted_limits n _ grow hn odd (fun i => (d i).2.2.1) (fun i => (d i).2.2.2)⟩

end CircleGDLimits
