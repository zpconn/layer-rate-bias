module

public import CircleSeedIntegrability
public import CircleStats
import all CircleEscapeBridge
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Fixed physical time and vanishing deterministic step for the Gaussian circle benchmark. -/

public section
noncomputable section
namespace CircleEulerLimits
open Filter Topology MeasureTheory ProbabilityTheory CircleEscapeBridge CircleSeedIntegrability

/-- Displayed finite lower bound with the physical time and update count as separate arguments. -/
def eulerBound (m k : ℕ) (t : ℝ) : ℝ :=
  4096 * (m : ℝ)^3 * (k : ℝ)^2 / (Real.pi^2*t^2) *
    Real.exp (4*Real.log 2*(3:ℝ)^k - 896*(m:ℝ)^2/t*k)

private theorem exp_four_log_two (k : ℕ) :
    Real.exp (4*Real.log 2*(3:ℝ)^k) = ((2:ℝ)^(3^k : ℕ))^4 := by
  have h : Real.exp ((3:ℝ)^k*Real.log 2) = (2:ℝ)^(3^k : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.exp_log (by norm_num : (0:ℝ)<2)]
      using Real.exp_nat_mul (Real.log 2) (3^k)
  calc
    _ = Real.exp ((4:ℕ) * ((3:ℝ)^k * Real.log 2)) := by push_cast; congr 1; ring
    _ = _ := by rw [Real.exp_nat_mul, h]

/-- The finite Gaussian-box expression is exactly the stated function of equal time steps. -/
theorem mass_amplitude_eq_eulerBound (m k : ℕ) {t L : ℝ} (ht : 0<t) (hk : 0<k)
    (hL : L^2 = 64*(m:ℝ)/(t/k)) :
    Real.exp (-896*(m:ℝ)^2/(t/k)) * (amplitude m k L)^2 = eulerBound m k t := by
  have hm := Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hk' : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hr : -896*(m:ℝ)^2/(t/k) = -(896*(m:ℝ)^2/t*k) := by
    field_simp
  rw [eulerBound, sub_eq_add_neg, Real.exp_add, exp_four_log_two, hr]
  unfold amplitude
  rw [mul_pow, mul_pow, hL, div_pow, hm, div_div_eq_mul_div]
  ring

/-- The cubic iteration exponent defeats the cost linear in the number of steps. -/
theorem eulerBound_tendsto (m : ℕ) (hm : 1≤m) (t : ℝ) (ht : 0<t) :
    Tendsto (fun k : ℕ => eulerBound m k t) atTop atTop := by
  let a : ℝ := 4 * Real.log 2
  let c : ℝ := 896 * (m:ℝ)^2/t
  let d : ℝ := 4096 * (m:ℝ)^3 / (Real.pi^2*t^2)
  have ha : 0<a := by dsimp [a]; positivity
  have hm' : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hd : 0<d := by dsimp [d]; positivity
  have hr : Tendsto (fun k : ℕ => (k:ℝ)/(3:ℝ)^k) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<3)
  have hf : Tendsto (fun k : ℕ => a - c*((k:ℝ)/3^k)) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x:=a) (f:=atTop)).sub (hr.const_mul c)
  have hg := Tendsto.pos_mul_atTop ha hf (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3))
  have hexp : Tendsto (fun k : ℕ => Real.exp (a*3^k-c*k)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    refine hg.congr fun k => ?_
    have h3 : (3:ℝ)^k ≠ 0 := by positivity
    field_simp
  apply tendsto_atTop_mono' atTop _ (Tendsto.const_mul_atTop hd hexp)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hdk : d ≤ d*(k:ℝ)^2 := by nlinarith [mul_nonneg hd.le (sq_nonneg ((k:ℝ)-1)),
                                               mul_nonneg hd.le (sub_nonneg.mpr hk')]
  calc
    _ ≤ (d*(k:ℝ)^2)*Real.exp (a*3^k-c*k) := mul_le_mul_of_nonneg_right hdk (Real.exp_pos _).le
    _ = _ := by unfold eulerBound d a c; ring

/-- Divergent variance excludes convergence in root mean square to any fixed
square-integrable comparison, without a condition on the coupling. -/
theorem rms_tendsto_of_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (F : Ω → ℝ)
    (hY : ∀ k, MemLp (Y k) 2 μ) (hF : MemLp F 2 μ)
    (hvar : Tendsto (fun k => variance (Y k) μ) atTop atTop) :
    Tendsto (fun k => Real.sqrt (∫ ω, (Y k ω-F ω)^2 ∂μ)) atTop atTop := by
  have hs := Real.tendsto_sqrt_atTop.comp hvar
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hs.eventually_ge_atTop (b+Real.sqrt (variance F μ))] with k hk
  have hb : b ≤ Real.sqrt (variance (Y k) μ) - Real.sqrt (variance F μ) := by
    change b+Real.sqrt (variance F μ) ≤ Real.sqrt (variance (Y k) μ) at hk
    linarith
  exact hb.trans ((le_abs_self _).trans (CircleStats.sd_transfer (hY k) hF))

/-- Actual terminal population statistic after k steps, each of size t/k. -/
def eulerOutput (N m : ℕ) (t : ℝ) (k : ℕ) : Seed m → ℝ :=
  trainedMean (path N m (t/k)) k

/-- The explicit bound for every positive finite update count for which t/k ≤ 1. -/
theorem fixed_time_variance_lower (N m k : ℕ) (hN : 3≤N) (hm : 1≤m) (hk : 0<k)
    (t : ℝ) (ht : 0<t) (hkt : t≤k) :
    eulerBound m k t ≤ variance (eulerOutput N m t k) (seedLaw m) := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hη : 0<t/k := div_pos ht hk'
  have hcap : t/k ≤ 1 := (div_le_one hk').mpr hkt
  let L := Real.sqrt (64*(m:ℝ)/(t/k))
  have hm' : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hL : 0<L := by dsimp [L]; positivity
  have hscale : L^2 = 64*(m:ℝ)/(t/k) := Real.sq_sqrt (by positivity)
  rw [← mass_amplitude_eq_eulerBound m k ht hk hscale]
  exact (actual_bounds N m k hN hm (t/k) L 0 hη hcap hL hscale (by norm_num) (by norm_num)).1

/-- At fixed grid, width and positive physical time the actual finite-step
Gaussian variances diverge as the number of Euler steps increases. -/
theorem fixed_time_variance_tendsto (N m : ℕ) (hN : 3≤N) (hm : 1≤m) (t : ℝ) (ht : 0<t) :
    Tendsto (fun k => variance (eulerOutput N m t k) (seedLaw m)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (eulerBound_tendsto m hm t ht)
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop t] with k hk hkt
  exact fixed_time_variance_lower N m k hN hm hk t ht hkt

/-- In particular this covers any same-seed flow observable once its finite
second moment is established. No convergence of individual sample paths is
assumed. -/
theorem fixed_time_rms_tendsto (N m : ℕ) (hN : 3≤N) (hm : 1≤m) (t : ℝ) (ht : 0<t)
    (F : Seed m → ℝ) (hF : MemLp F 2 (seedLaw m)) :
    Tendsto (fun k => Real.sqrt (∫ ω, (eulerOutput N m t k ω - F ω)^2 ∂(seedLaw m)))
      atTop atTop :=
  rms_tendsto_of_variance _ _ (fun k => trained_memLp N m k (t/k) 2 (by norm_num))
    hF (fixed_time_variance_tendsto N m hN hm t ht)

/-- For width N^32, a lower bound c log N on the update count makes the
Gaussian-box cost negligible when c log 3 > 64. -/
theorem cost_ratio_of_log_schedule (T : ℕ → ℕ) (c : ℝ) (hc : 64<c*Real.log 3)
    (hT : ∀ᶠ N : ℕ in atTop, c*Real.log N ≤ (T N:ℝ)) :
    Tendsto (fun N : ℕ => (N:ℝ)^64/(3:ℝ)^(T N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hneg : 64-c*Real.log 3<0 := by linarith
  have hupper := Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg hneg)
  apply squeeze_zero' _ _ hupper
  · exact .of_forall fun N => by positivity
  · filter_upwards [hT,eventually_ge_atTop 1] with N hn hN
    have hN' : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    change _ ≤ Real.exp ((64-c*Real.log 3)*Real.log N)
    have hnum : (N:ℝ)^64 = Real.exp ((64:ℝ)*Real.log N) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hN'] using
        (Real.exp_nat_mul (Real.log (N:ℝ)) 64).symm
    have hden : (3:ℝ)^(T N) = Real.exp ((T N:ℝ)*Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<3)]
    rw [hnum,hden,←Real.exp_sub,Real.exp_le_exp]
    have hmul := mul_le_mul_of_nonneg_right hn (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<3)))
    linarith only [hmul]

/-- The same finite-box variance bound specialized to unit step. -/
def unitBound (m T : ℕ) : ℝ :=
  (4096*(m:ℝ)^3/Real.pi^2) * Real.exp (4*Real.log 2*(3:ℝ)^T - 896*(m:ℝ)^2)

private theorem mass_amplitude_eq_unitBound (m T : ℕ) {L : ℝ} (hL : L^2 = 64*(m:ℝ)) :
    Real.exp (-896*(m:ℝ)^2/1) * (amplitude m T L)^2 = unitBound m T := by
  rw [unitBound, sub_eq_add_neg, Real.exp_add, exp_four_log_two, amplitude, mul_pow, mul_pow,
    hL, div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  ring_nf

theorem unitBound_growing_tendsto (T : ℕ → ℕ) (c : ℝ) (hc : 64<c*Real.log 3)
    (hT : ∀ᶠ N : ℕ in atTop, c*Real.log N ≤ (T N:ℝ)) :
    Tendsto (fun N : ℕ => unitBound (N^32) (T N)) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hl3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  have hc' : 0<c := by by_contra! h; linarith [mul_nonpos_of_nonpos_of_nonneg h hl3.le]
  have htime := tendsto_atTop_mono' atTop hT (Tendsto.const_mul_atTop hc' hlog)
  have hp : Tendsto (fun N : ℕ => (3:ℝ)^(T N)) atTop atTop := by
    simpa only [Function.comp_def, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<3)]
      using Real.tendsto_exp_atTop.comp (Tendsto.atTop_mul_const hl3 htime)
  let a : ℝ := 4*Real.log 2
  have ha : 0<a := by dsimp [a]; positivity
  have hr := cost_ratio_of_log_schedule T c hc hT
  have hf : Tendsto (fun N:ℕ => a-896*((N:ℝ)^64/3^(T N))) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x:=a) (f:=atTop)).sub (hr.const_mul 896)
  have he : Tendsto (fun N:ℕ => Real.exp (a*3^(T N)-896*(N:ℝ)^64)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    refine (Tendsto.pos_mul_atTop ha hf hp).congr fun N => ?_
    have h3 : (3:ℝ)^(T N) ≠ 0 := by positivity
    field_simp
  have hpre : (0:ℝ)<4096/Real.pi^2 := by positivity
  apply tendsto_atTop_mono' atTop _ (Tendsto.const_mul_atTop hpre he)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hpow : (1:ℝ) ≤ ((N:ℝ)^32)^3 := one_le_pow₀ (one_le_pow₀ hn)
  have hpre' : 4096/Real.pi^2 ≤ 4096*((N:ℝ)^32)^3/Real.pi^2 := by gcongr; linarith
  have hsum : ((N:ℝ)^32)^2 = N^64 := by ring
  simpa only [unitBound, Nat.cast_pow, hsum, a] using
    mul_le_mul_of_nonneg_right hpre' (Real.exp_pos (a*3^(T N)-896*(N:ℝ)^64)).le

/-- At unit step, any update count eventually at least c log N with
c log 3 > 64 forces the variance to diverge at width N^32. -/
theorem growing_variance_tendsto (T : ℕ → ℕ) (c : ℝ) (hc : 64<c*Real.log 3)
    (hT : ∀ᶠ N : ℕ in atTop, c*Real.log N ≤ (T N:ℝ)) :
    Tendsto (fun N : ℕ => variance (trainedMean (path N (N^32) 1) (T N)) (seedLaw (N^32)))
      atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (unitBound_growing_tendsto T c hc hT)
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hm : 1≤N^32 := one_le_pow₀ (by omega)
  have hm' : (0:ℝ)<(N^32:ℕ) := by exact_mod_cast (by omega : 0<N^32)
  let L := Real.sqrt (64*((N^32:ℕ):ℝ))
  have hL : 0<L := by dsimp [L]; positivity
  have hscale : L^2 = 64*((N^32:ℕ):ℝ) := Real.sq_sqrt (by positivity)
  rw [← mass_amplitude_eq_unitBound _ _ hscale]
  exact (actual_bounds N (N^32) (T N) hN hm 1 L 0 (by norm_num) (by norm_num)
    hL (by simpa using hscale) (by norm_num) (by norm_num)).1

/-- The middle logarithmic cap in the manuscript, with all Gaussian seeds. -/
theorem middle_variance_tendsto :
    Tendsto (fun N : ℕ => variance (trainedMean (path N (N^32) 1)
      ⌈60*Real.log N⌉₊) (seedLaw (N^32))) atTop atTop :=
  growing_variance_tendsto _ 60 (by linarith [Real.log_three_gt_d9])
    (.of_forall fun N => Nat.le_ceil _)

/-- The deterministic full-residual horizon at unit step. -/
def longCap (N : ℕ) : ℕ :=
  ⌈2*Real.pi^2*(N:ℝ)^2*Real.log (2*Real.sqrt 12*(N:ℝ)^(7/2:ℝ))⌉₊

private theorem longCap_lower :
    ∀ᶠ N : ℕ in atTop, 60*Real.log N ≤ (longCap N:ℝ) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by linarith
  have hn0 : (0:ℝ) < N := by linarith
  have hs : 1≤2*Real.sqrt 12 := by linarith [Real.one_le_sqrt.mpr (by norm_num : (1:ℝ)≤12)]
  have harg : (N:ℝ)≤2*Real.sqrt 12*(N:ℝ)^(7/2:ℝ) := by
    calc
      _ = (N:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (N:ℝ)^(7/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hs
  have hfac : (60:ℝ) ≤ 2*Real.pi^2*(N:ℝ)^2 := by
    calc
      _ ≤ 2*(3:ℝ)^2*(3:ℝ)^2 := by norm_num
      _ ≤ _ := by gcongr; linarith [Real.pi_gt_three]
  exact (mul_le_mul hfac (Real.log_le_log hn0 harg) (Real.log_nonneg hn1)
    (by positivity)).trans (Nat.le_ceil _)

theorem long_variance_tendsto :
    Tendsto (fun N : ℕ => variance (trainedMean (path N (N^32) 1)
      (longCap N)) (seedLaw (N^32))) atTop atTop :=
  growing_variance_tendsto _ 60 (by linarith [Real.log_three_gt_d9]) longCap_lower

/-- At unit step and positive width, from the second update onward the reference
cap on the positive box costs at most half the escaping amplitude. -/
theorem half_amplitude (m T : ℕ) (hm : 1≤m) (hT : 2≤T) {L : ℝ}
    (hL : 1 ≤ L^2) : referenceCap m L ≤ amplitude m T L/2 := by
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  have hs : 1≤Real.sqrt m := (Real.one_le_sqrt).2 hm'
  have hbase : 1≤Real.sqrt m*L^2 := one_le_mul_of_one_le_of_one_le hs (by linarith)
  have hbase0 : 0≤Real.sqrt m*L^2 := by positivity
  have hr : Real.sqrt 2 ≤ 3/2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hpow : (256:ℝ) ≤ (2:ℝ)^(3^T : ℕ) := by
    calc
      _ = (2:ℝ)^8 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) ((by decide : 8≤3^2).trans
        (Nat.pow_le_pow_right (by decide : 0<3) hT))
  have hbig : 64*Real.pi ≤ ((2:ℝ)^(3^T : ℕ))^2 := by
    nlinarith [Real.pi_lt_four, sq_nonneg ((2:ℝ)^(3^T : ℕ)-256)]
  calc
    referenceCap m L ≤ 32*(Real.sqrt m*L^2) := by
      unfold referenceCap
      nlinarith only [hbase, mul_le_mul_of_nonneg_right hr hbase0]
    _ ≤ (Real.sqrt m*L^2)*((2:ℝ)^(3^T:ℕ))^2 / (2*Real.pi) := by
      apply (le_div_iff₀ (by positivity)).2
      linarith only [mul_le_mul_of_nonneg_left hbig hbase0]
    _ = _ := by unfold amplitude; ring

/-- Uniform finite-cap bound for the actual paired MSE, for every benchmark
coefficient in the interval [0,1]. -/
theorem unit_paired_lower (N m T : ℕ) (hN : 3≤N) (hm : 1≤m) (hT : 2≤T)
    (b : ℝ) (hb : 0≤b) (hb' : b≤1) :
    unitBound m T/4 ≤ ∫ ω, (trainedMean (path N m 1) T ω-reference N m b ω)^2 ∂seedLaw m := by
  have hm' : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  let L := Real.sqrt (64*(m:ℝ))
  have hL : 0<L := by dsimp [L]; positivity
  have hscale : L^2=64*(m:ℝ) := Real.sq_sqrt (by positivity)
  have hbnd := (actual_bounds N m T hN hm 1 L b (by norm_num) (by norm_num)
    hL (by simpa using hscale) hb hb').2
  have hhalf := half_amplitude m T hm hT (by rw [hscale]; linarith [show (1:ℝ)≤m by exact_mod_cast hm])
  have ha : 0≤amplitude m T L := by unfold amplitude; positivity
  have hle : amplitude m T L/2 ≤ max (amplitude m T L-referenceCap m L) 0 :=
    (show amplitude m T L/2 ≤ amplitude m T L-referenceCap m L by linarith).trans (le_max_left ..)
  rw [← mass_amplitude_eq_unitBound m T hscale]
  refine le_trans ?_ hbnd
  calc
    _ = Real.exp (-896*(m:ℝ)^2/1)*(amplitude m T L/2)^2 := by ring
    _ ≤ _ := by gcongr

theorem growing_paired_tendsto (T : ℕ → ℕ) (c : ℝ) (hc : 64<c*Real.log 3)
    (hT : ∀ᶠ N : ℕ in atTop, c*Real.log N ≤ (T N:ℝ))
    (b : ℕ → ℝ) (hb : ∀ N, 0≤b N ∧ b N≤1) :
    Tendsto (fun N : ℕ => ∫ ω, (trainedMean (path N (N^32) 1) (T N) ω -
      reference N (N^32) (b N) ω)^2 ∂seedLaw (N^32)) atTop atTop := by
  have hc' : 0<c := by
    by_contra! h
    linarith [mul_nonpos_of_nonpos_of_nonneg h (Real.log_nonneg (by norm_num : (1:ℝ)≤3))]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htime := tendsto_atTop_mono' atTop hT (Tendsto.const_mul_atTop hc' hlog)
  have hbound := (unitBound_growing_tendsto T c hc hT).atTop_mul_const (by norm_num : (0:ℝ)<1/4)
  apply tendsto_atTop_mono' atTop _ hbound
  filter_upwards [eventually_ge_atTop 3, htime.eventually_ge_atTop 2] with N hN hTN
  have hm : 1≤N^32 := one_le_pow₀ (by omega)
  have hTN' : 2≤T N := by exact_mod_cast hTN
  simpa only [mul_one_div] using unit_paired_lower N (N^32) (T N) hN hm hTN'
    (b N) (hb N).1 (hb N).2

theorem middle_long_paired_tendsto (b : ℕ → ℝ) (hb : ∀ N, 0≤b N ∧ b N≤1) :
    (Tendsto (fun N : ℕ => ∫ ω, (trainedMean (path N (N^32) 1) ⌈60*Real.log N⌉₊ ω -
      reference N (N^32) (b N) ω)^2 ∂seedLaw (N^32)) atTop atTop) ∧
    Tendsto (fun N : ℕ => ∫ ω, (trainedMean (path N (N^32) 1) (longCap N) ω -
      reference N (N^32) (b N) ω)^2 ∂seedLaw (N^32)) atTop atTop := by
  have hc : 64 < 60*Real.log 3 := by linarith [Real.log_three_gt_d9]
  exact ⟨growing_paired_tendsto _ 60 hc (.of_forall fun N => Nat.le_ceil _) b hb,
    growing_paired_tendsto _ 60 hc longCap_lower b hb⟩

/-- Taking logs of the actual mass times squared amplitude loses only the
nonnegative logarithm of its prefactor. -/
theorem width_log_of_mass (m T : ℕ) (hm : 1≤m) (η V L : ℝ)
    (hη : 0<η) (hη' : η≤1)
    (hscale : L^2 = 64*(m:ℝ)/η)
    (hV : Real.exp (-896*(m:ℝ)^2/η)*(amplitude m T L)^2 ≤ V) :
    4*Real.log 2*(3:ℝ)^T ≤ 896*(m:ℝ)^2/η + Real.log V := by
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  have hηsq : η^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hη') hη.le]
  have hsize : Real.pi^2*η^2 ≤ 4096*(m:ℝ)^3 := by
    calc
      _ ≤ 4^2*(1:ℝ) := by gcongr; exact Real.pi_lt_four.le
      _ ≤ 4096 * (1:ℝ)^3 := by norm_num
      _ ≤ _ := by gcongr
  have hpref : 1 ≤ 4096*(m:ℝ)^3/(Real.pi^2*η^2) := (one_le_div (by positivity)).2 hsize
  let x := 4*Real.log 2*(3:ℝ)^T - 896*(m:ℝ)^2/η
  have he : Real.exp x ≤ V := by
    calc
      _ ≤ (4096*(m:ℝ)^3/(Real.pi^2*η^2))*Real.exp x :=
        le_mul_of_one_le_left (Real.exp_pos _).le hpref
      _ = Real.exp (-896*(m:ℝ)^2/η) * (amplitude m T L)^2 := by
        dsimp only [x]
        rw [sub_eq_add_neg, Real.exp_add, exp_four_log_two, amplitude, mul_pow, mul_pow,
          div_pow, Real.sq_sqrt (Nat.cast_nonneg m), hscale]
        rw [show -896*(m:ℝ)^2/η = -(896*(m:ℝ)^2/η) by ring]
        ring
      _ ≤ _ := hV
  have hlog := (Real.le_log_iff_exp_le ((Real.exp_pos x).trans_le he)).2 he
  dsimp [x] at hlog
  linarith

/-- Finite necessary width for bounded raw variance. -/
theorem width_necessary (N m T : ℕ) (hN : 3≤N) (hm : 1≤m) (η V : ℝ)
    (hη : 0<η) (hη' : η≤1)
    (hV : variance (trainedMean (path N m η) T) (seedLaw m) ≤ V) :
    4*Real.log 2*(3:ℝ)^T ≤ 896*(m:ℝ)^2/η + Real.log V := by
  let L := Real.sqrt (64*(m:ℝ)/η)
  have hL : 0<L := by dsimp [L]; positivity
  have hs : L^2 = 64*(m:ℝ)/η := Real.sq_sqrt (by positivity)
  exact width_log_of_mass m T hm η V L hη hη' hs
    ((actual_bounds N m T hN hm η L 0 hη hη' hL hs (by norm_num) (by norm_num)).1.trans hV)

end CircleEulerLimits
