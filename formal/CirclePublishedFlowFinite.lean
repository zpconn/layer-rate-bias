module

public import CircleVariableFlowSchedule
public import CircleUniformRadius
public import CirclePublishedFlowEvent
public import CirclePublishedFourth
public import CircleVariableFlow
import all CircleVariableFlow
import all CircleFlowMoments
import all CircleFlowPath
import all CircleActualTracking
import all CircleGaussianTracking
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleKernelGD
import Mathlib.Tactic

/-! Integration of the finite physical-time bound for the equal-rate flow
against the original Gaussian seed distribution. -/
@[expose] public section
noncomputable section
namespace CirclePublishedFlowFinite
open Real MeasureTheory Set CircleFlowPath CircleEscapeBridge CircleGaussianTracking
  CircleTangentDrift CircleFlowMoments CircleActualTracking CirclePublishedFlowEvent

private theorem integrate {n m : ℕ} (hn : 3≤n+1) (hm : 0<m) {T d ρ B : ℝ}
    (ht : 0≤T) (dp : 0≤d) (dm : d≤m) (rp : 0≤ρ) (rc : ρ≤1) (uc : 64*sqrt (d/m)≤1) (bp : 0≤B)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T (z ω))
    (meas : Measurable fun ω => z ω T)
    (path : ∀ ω, StrongInit (n+1) m ρ (64*sqrt (d/m)) ω →
      ‖gridR (n+1) ω‖≤2+sqrt (8*d) →
      |mean (z ω T)-reference (n+1) m (CircleVariableFlow.stopped n T) ω|≤B) :
    let Δ := min 1 (8*(((n+1:ℕ):ℝ)+1)^2*exp (-d))
    sqrt (∫ ω, (mean (z ω T)-reference (n+1) m (CircleSpectrum.weight 1 n) ω)^2 ∂seedLaw m) ≤
      B+20*(1+sqrt T+T/sqrt m)*Δ^(1/4:ℝ)+sqrt 2*exp (-(CircleKernelGD.gamma (n+1)*T)) := by
  intro Δ
  let μ := seedLaw m
  obtain ⟨G,measG,gEvent,tail⟩ := event (N:=n+1) hm dp dm rp rc uc
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have gp := (by positivity : 0≤3/π^2).trans (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have z0 : 0≤CircleVariableFlow.multiplier n T := exp_nonneg _
  have z1 : CircleVariableFlow.multiplier n T≤1 := exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg gp ht))
  have lo : 0≤CircleVariableFlow.stopped n T := mul_nonneg wb.1 (sub_nonneg.mpr z1)
  have hi : CircleVariableFlow.stopped n T≤1 := (mul_le_of_le_one_right wb.1 (sub_le_self _ z0)).trans wb.2
  let Y := fun ω => mean (z ω T)
  let X := Y-reference (n+1) m (CircleVariableFlow.stopped n T)
  have hd : MemLp X 4 μ :=
    (gaussian_flow_fourth_sharp (N:=n+1) (by omega) hm (by norm_num : 0<(1:ℝ)) (by norm_num) ht lo hi z start flow meas).1
  have good (ω) (h : ω∈G) : |X ω|≤B :=
    path ω (gEvent ω h).1 (gEvent ω h).2.1
  have norm := CirclePublishedFourth.twenty hn hm ht lo hi z start flow meas
  have fourth := (CircleGaussianTracking.fourth_integral hd).le.trans (pow_le_pow_left₀ lpNorm_nonneg norm 4)
  have rms := CircleFlowTracking.all_seed_rms measG (CircleGaussianTracking.square_mem hd) bp
    (by positivity : 0≤20*(1+sqrt T+T/sqrt m)) good tail fourth
  have mY : MemLp Y 2 μ := by
    have id : Y=X+reference (n+1) m (CircleVariableFlow.stopped n T) := by dsimp [X];abel
    rw [id]
    exact (hd.mono_exponent (by norm_num)).add (CircleSeedIntegrability.reference_memLp _ _ _ 2 (by norm_num))
  have pay := CircleVariableFlow.lag hn hm T Y mY
  have nn : 0≤Δ := le_min zero_le_one (by positivity)
  have root : sqrt (sqrt Δ)=Δ^(1/4:ℝ) := by
    rw [sqrt_eq_rpow,sqrt_eq_rpow,←rpow_mul nn];norm_num
  change sqrt (∫ ω, (X ω)^2 ∂μ)≤B+20*(1+sqrt T+T/sqrt m)*sqrt (sqrt Δ) at rms
  rw [root] at rms
  exact pay.trans (add_le_add_left rms _)

/-- The explicit intermediate inequality in followup/flow.md, for every
finite admissible design and every Gaussian-measurable actual flow endpoint. -/
theorem finite {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) {T d : ℝ}
    (ht : 0≤T) (dp : 0≤d) (dm : d≤m)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T (z ω))
    (meas : Measurable fun ω => z ω T) :
    let N : ℝ := (n+1:ℕ)
    let R := 2+sqrt (8*d)
    let u := 64*sqrt (d/m)
    let lam := 1/(π*N)^2
    let ρ := 4*R/(lam*sqrt m)
    let e := 30*ρ+3*u
    let b := CircleSpectrum.weight 1 n
    let γ := CircleKernelGD.gamma (n+1)
    let Δ := min 1 (8*(N+1)^2*exp (-d))
    ρ≤1 → u≤1 → e≤lam/2 →
    sqrt (∫ ω, (mean (z ω T)-reference (n+1) m b ω)^2 ∂seedLaw m) ≤
      e*R*(b/γ+2*(1+b)/lam)+20*(1+sqrt T+T/sqrt m)*Δ^(1/4:ℝ)+sqrt 2*exp (-(γ*T)) := by
  intro N R u lam ρ e b γ Δ rc uc small
  have rp : 0<ρ := by dsimp [ρ,R,lam,N];positivity
  have up : 0≤u := by dsimp [u];positivity
  have wb : 0≤b := (CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))).1
  have gp : 0≤γ := (by positivity : 0≤3/π^2).trans (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have pos : 0≤e*R*(b/γ+2*(1+b)/lam) := by dsimp [e,R,lam,N];positivity
  apply integrate hn hm ht dp dm rp.le rc uc pos z start flow meas
  intro ω init residual
  have result := CircleUniformRadius.good_path hn ho hm ht rp rc up small (R:=R) (le_refl ρ) (z ω) (flow ω)
  rw [start ω] at result
  exact result init.good init.gram init.row residual

open CircleVariableFlowSchedule in
/-- One measurable set works simultaneously for every actual flow and all
times after the long physical clock, uniformly over widths at least N^16. -/
theorem long_fit {n m : ℕ} (hn : 65536≤n+1) (ho : Odd (n+1)) (hw : (n+1)^16≤m) :
    let N : ℝ := (n+1:ℕ)
    ∃ G : Set (Seed m), MeasurableSet G ∧ (seedLaw m).real Gᶜ≤32/N^126 ∧
      ∀ ω∈G, ∀ T : ℝ, 0≤T → long N≤T → ∀ z : ℝ→State m, z 0=ω →
        IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T z →
        ‖gridR (n+1) (z T)‖≤1/N^3 := by
  intro x
  let r := 4*R x/(gap x*sqrt m)
  have hm : 0<m := (pow_pos (Nat.succ_pos n) _).trans_le hw
  have cond := conditions hn hw
  have dp : 0≤d x := zero_le_one.trans cond.1
  have lp : 0<gap x := by dsimp [gap,x];positivity
  have rp : 0<r := by dsimp [r,R];positivity
  have u0 : 0≤u x m := by unfold u;positivity
  have comparison : r≤rho x m := by
    have eq : 8*r=rho x m := by dsimp [r,rho,CircleVariableFlowSchedule.U];ring
    linarith only [rp,eq]
  have rc := comparison.trans cond.2.2.1
  have small : 30*r+3*u x m≤gap x/2 := by
    have s := cond.2.2.2.2
    change 2*(2*(30*rho x m+3*u x m))≤gap x at s
    linarith only [s,comparison,rp,u0]
  obtain ⟨G,ms,gg,tail⟩ := event (N:=n+1) hm dp cond.2.1 rp.le rc cond.2.2.2.1
  refine ⟨G,ms,tail.trans ((min_le_right _ _).trans (failure (x:=x) (by dsimp [x];exact_mod_cast Nat.succ_pos n))),?_⟩
  intro ω g T ht late z start flow
  obtain ⟨init,residual,_⟩ := gg ω g
  have path := CircleUniformRadius.confinement (by omega : 3≤n+1) ho hm ht rp rc u0 small
    (R:=R x) (le_refl r) z flow
  rw [start] at path
  have decay := (path init.good init.gram init.row residual T ⟨ht,le_rfl⟩).2.1
  exact decay.trans (fit_clock (by dsimp [x];exact_mod_cast hn) late)

end CirclePublishedFlowFinite
