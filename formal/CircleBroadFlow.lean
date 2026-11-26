module

public import CircleVariableFlow
public import CircleVariableFlowSchedule
public import CircleComparison
import all CircleComparison
import all CircleSeedIntegrability
import all CircleVariableFlowSchedule
import all CircleGaussianTracking
import all CircleVariableFlow
import all CircleFlowMoments
import all CircleEscapeBridge
import Mathlib.Tactic

/-! The long-time Gaussian paired error of every measurable circle flow at any
width above the polynomial threshold. -/
@[expose] public section
noncomputable section
namespace CircleBroadFlow
open Real MeasureTheory CircleFlowPath CircleEscapeBridge CircleFlowMoments CircleFlowTracking
  CircleVariableFlowSchedule

/-- A measurable choice for the original Gaussian network, fixed over all
physical times. Such a choice exists at every nondegenerate odd grid. -/
structure Selection (N m : ℕ) where
  path : Seed m → ℝ → State m
  start : ∀ ω, path ω 0=ω
  flow : ∀ T, 0≤T → ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T (path ω)
  meas : ∀ T, 0≤T → Measurable fun ω => path ω T

theorem nonempty (N m : ℕ) (hn : 3≤N) : Nonempty (Selection N m) := by
  obtain ⟨z,start,sol⟩ := CircleGaussianTracking.exists_actual_selector N m hn (τ:=1) (by norm_num) (by norm_num)
  exact ⟨⟨z,start,fun T ht => (sol T ht).1,fun T ht => (sol T ht).2⟩⟩

def rms {n m : ℕ} (z : Selection (n+1) m) (T : ℝ) :=
  sqrt (∫ ω, (mean (z.path ω T)-reference (n+1) m (CircleSpectrum.weight 1 n) ω)^2 ∂seedLaw m)

/-- All times through H, uniformly in the width, with separate width and
exceptional-event terms as in followup/flow.md. -/
theorem through_horizon {n m : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hm : (n+1)^16≤m)
    (z : Selection (n+1) m) {T : ℝ} (ht : 0≤T) (cap : T≤(horizon (n+1:ℕ):ℝ)) :
    let N : ℝ := (n+1:ℕ)
    rms z T ≤ constant*(N^4*log N/sqrt m+sqrt N*sqrt (log N)/N^31)+sqrt 2*exp (-(CircleKernelGD.gamma (n+1)*T)) := by
  intro x
  have c := conditions hn hm
  have pos : 0<m := (pow_pos (Nat.succ_pos n) _).trans_le hm
  have val := CircleVariableFlow.finite (by omega : 3≤n+1) ho pos ht (zero_le_one.trans c.1) c.2.1 z.path z.start
    (z.flow T ht) (z.meas T ht) c.2.2.1 c.2.2.2.1 c.2.2.2.2
  have kp : 0≤fourth T m := by
    have a : 0≤gaussianSquareNorm := lpNorm_nonneg
    have b : 0≤lossConstant := by unfold lossConstant;positivity
    unfold fourth;positivity
  have ep : 0≤bad x := by unfold bad;positivity
  have remove := mul_le_mul_of_nonneg_left (rpow_le_rpow (le_min zero_le_one ep) (min_le_right 1 (bad x)) (by norm_num : 0≤(1/4:ℝ))) kp
  change rms z T≤6*error x m*U x+fourth T m*(min 1 (bad x))^(1/4:ℝ)+_ at val
  exact val.trans (add_le_add_left ((add_le_add_right remove _).trans (all_times hn hm cap)) _)

/-- Every sufficiently wide actual flow at times that have resolved the
constant Fourier mode. The constants are uniform in the seed selection. -/
theorem rate {n m k p : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hm : (n+1)^16≤m)
    (z : Selection (n+1) m) (size : ((n+1:ℕ):ℝ)^(k+4)≤sqrt m) (hk : k≤30)
    {T : ℝ} (ht : 0≤T) (cap : T≤(horizon (n+1:ℕ):ℝ))
    (clock : (p:ℝ)*log (n+1:ℕ)≤CircleKernelGD.gamma (n+1)*T) :
    let x : ℝ := (n+1:ℕ)
    rms z T≤2*constant*log x/x^k+sqrt 2/x^p := by
  intro x
  have c := conditions hn hm
  have pos : 0<m := (pow_pos (Nat.succ_pos n) _).trans_le hm
  have val := CircleVariableFlow.finite (by omega : 3≤n+1) ho pos ht (zero_le_one.trans c.1) c.2.1 z.path z.start
    (z.flow T ht) (z.meas T ht) c.2.2.1 c.2.2.2.1 c.2.2.2.2
  exact val.trans (stopped hn hm size hk ht cap clock)

private theorem width8 {N m : ℕ} (hm : N^16≤m) : (N:ℝ)^8≤sqrt m := by
  have c := sqrt_le_sqrt (show (N:ℝ)^16≤m by exact_mod_cast hm)
  rwa [show (N:ℝ)^16=((N:ℝ)^8)^2 by ring,sqrt_sq (by positivity)] at c

/-- The manuscript's uniform long-time O(log(N)/N⁴) assertion at every
width m≥N¹⁶, valid at the specified physical time and its ceiling. -/
theorem long_rate {n m : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hm : (n+1)^16≤m)
    (z : Selection (n+1) m) {T : ℝ} (after : long (n+1:ℕ)≤T) (cap : T≤(horizon (n+1:ℕ):ℝ)) :
    let x : ℝ := (n+1:ℕ)
    rms z T≤(2*constant+sqrt 2)*log x/x^4 := by
  intro x
  have c := clocks (N:=n+1) (by omega)
  have st : 60*log x≤T := c.2.2.1.trans after
  have xp : 0<x := Nat.cast_pos.mpr (Nat.succ_pos _)
  have x1 : 1≤x := by dsimp [x];exact_mod_cast Nat.succ_pos n
  have l1 : 1≤log x := CircleVariableFlowSchedule.log_one (by dsimp [x];exact_mod_cast hn)
  have gp : 0≤CircleKernelGD.gamma (n+1) :=
    (by positivity : 0≤(3:ℝ)/π^2).trans (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have ht : 0≤T := (mul_nonneg (by norm_num) (log_nonneg x1)).trans st
  have clk : (4:ℝ)*log x≤CircleKernelGD.gamma (n+1)*T := by
    have h := c.2.1.trans (mul_le_mul_of_nonneg_left st gp)
    change 18*log x≤_ at h
    linarith [log_nonneg x1]
  have q := rate (k:=4) (p:=4) hn ho hm z (width8 hm) (by decide) ht cap clk
  apply q.trans
  rw [←add_div,add_mul]
  apply div_le_div_of_nonneg_right _ (pow_nonneg xp.le _)
  linarith [mul_le_mul_of_nonneg_left l1 (sqrt_nonneg 2)]

/-- The very same constant applies to the rounded deterministic deadline. -/
theorem rounded_long {n m : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hm : (n+1)^16≤m)
    (z : Selection (n+1) m) :
    let x : ℝ := (n+1:ℕ)
    rms z (horizon x)≤(2*constant+sqrt 2)*log x/x^4 := by
  exact long_rate hn ho hm z (clocks (N:=n+1) (by omega)).2.2.2 le_rfl

/-- A time at least π² log N already has O(N⁻³) RMS discrepancy, uniformly
at all widths m≥N¹⁶ and physical times through the long ceiling. -/
theorem short_rate {n m : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hm : (n+1)^16≤m)
    (z : Selection (n+1) m) {T : ℝ} (after : π^2*log (n+1:ℕ)≤T) (cap : T≤(horizon (n+1:ℕ):ℝ)) :
    let x : ℝ := (n+1:ℕ)
    rms z T≤(2*constant+sqrt 2)/x^3 := by
  intro x
  have xp : 0<x := Nat.cast_pos.mpr (Nat.succ_pos _)
  have x1 : 1≤x := by dsimp [x];exact_mod_cast Nat.succ_pos n
  have gp : 0≤CircleKernelGD.gamma (n+1) := (by positivity : 0≤(3:ℝ)/π^2).trans (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have ht : 0≤T := (mul_nonneg (sq_nonneg π) (log_nonneg x1)).trans after
  have clk := (clocks (N:=n+1) (by omega)).1.trans (mul_le_mul_of_nonneg_left after gp)
  have q := rate (k:=4) (p:=3) hn ho hm z (width8 hm) (by decide) ht cap clk
  apply q.trans
  rw [add_div]; apply add_le_add_left
  have cc : 0≤2*constant := mul_nonneg (by norm_num) CircleVariableFlowSchedule.constant_nonneg
  have lx : log x≤x := by linarith [log_le_sub_one_of_pos xp]
  change 2*constant*log x/x^4≤2*constant/x^3
  calc _ ≤ 2*constant*x/x^4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left lx cc) (by positivity)
       _ = _ := by field_simp


open Filter Topology in
/-- Arbitrary-width transfer of the two circle kernel moment constants at every
physical time between the short and long deadlines. -/
theorem population_limits (n m : ℕ→ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3≤n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, (n i+1)^16≤m i)
    (F : ∀ i, Selection (n i+1) (m i)) (T : ℕ→ℝ)
    (after : ∀ i, π^2*log (n i+1:ℕ)≤T i) (before : ∀ i, T i≤(horizon (n i+1:ℕ):ℝ)) :
    let Y i ω := mean ((F i).path ω (T i))
    Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ ω, Y i ω ∂seedLaw (m i))-1)) atTop (𝓝 (-(π^2/36))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (seedLaw (m i))) atTop (𝓝 (7*π^2/1620)) := by
  intro Y
  let x (i : ℕ) : ℝ := (n i:ℝ)+1
  let C := 2*constant+sqrt 2
  have xp (i) : 0<x i := by dsimp [x];positivity
  have ht (i) : 0≤T i := (mul_nonneg (sq_nonneg π) (log_nonneg (show (1:ℝ)≤(n i+1:ℕ) by exact_mod_cast Nat.succ_pos _))).trans (after i)
  have pos (i) : 0<m i := (pow_pos (Nat.succ_pos _) _).trans_le (hm i)
  have hY (i) : MemLp (Y i) 2 (seedLaw (m i)) := by
    let Z := reference (n i+1) (m i) 0
    have p := gaussian_flow_fourth_sharp (N:=n i+1) (Nat.succ_pos _) (pos i) (by norm_num : 0<(1:ℝ)) (by norm_num)
      (ht i) (by norm_num : (0:ℝ)≤0) (by norm_num) (F i).path (F i).start ((F i).flow _ (ht i)) ((F i).meas _ (ht i))
    have hd : MemLp (Y i-Z) 2 (seedLaw (m i)) := p.1.mono_exponent (by norm_num)
    have sum := hd.add (CircleSeedIntegrability.reference_memLp (n i+1) (m i) 0 2 (by norm_num))
    exact (sub_add_cancel (Y i) Z) ▸ sum
  have xinf : Tendsto x atTop atTop := CircleComparison.grown n grow
  have lim : Tendsto (fun i => C/x i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop xinf
  have track : Tendsto (fun i => x i^2*rms (F i) (T i)) atTop (𝓝 0) := by
    apply squeeze_zero' (.of_forall fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) _ lim
    filter_upwards [grow.eventually_ge_atTop 65536] with i grid
    have r := short_rate (n:=n i) (by omega) (ho i) (hm i) (F i) (after i) (before i)
    have q : rms (F i) (T i)≤C/(x i)^3 := by simpa only [C,x,Nat.cast_add,Nat.cast_one] using r
    exact (mul_le_mul_of_nonneg_left q (sq_nonneg _)).trans_eq (by field_simp)
  have v := CircleComparison.gaussian_reference_transfer n m grow hn ho pos (τ:=1) (by norm_num) Y hY track
  constructor
  · convert v.1.neg using 2 with i <;> ring
  · convert v.2 using 2;ring
end CircleBroadFlow
