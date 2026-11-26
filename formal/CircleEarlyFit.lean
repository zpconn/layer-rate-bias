module

public import CircleShortFlowProjection
public import CircleFourthFeature
public import CircleDiscreteMoments
public import CircleConditioning
import all CircleFourthEigen
import all CircleFourthFeature
import all CircleConditioning
import all CircleKernelGD
import all CircleGridSpectrum
import all CircleSpectralPathLength
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleCapMoments
import all CircleSharpEvent
import Mathlib.Tactic

/-! A fourth Fourier mode which obstructs full training fit throughout both
logarithmic stopping windows. -/
public section
noncomputable section
namespace CircleEarlyFit
open Real MeasureTheory ProbabilityTheory Set Filter Topology
  CircleFourthEigen CircleFourthFeature CircleEscapeBridge CircleInitializationCheck
  CircleCapMoments CircleGridSpectrum CircleSpectralPathLength CircleDiscreteTracking
  CircleKernelGD CircleActualTracking CircleTangentDrift CircleFlowPath

variable {N : ℕ} [NeZero N]

theorem short_le_medium (N : ℕ) (hn : 1≤N) : short N≤medium N := by
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_right _ (log_nonneg (by exact_mod_cast hn))
  nlinarith [pi_lt_four,pi_pos,sq_nonneg (π-4),mul_pos (sub_pos.mpr pi_lt_four) (show 0<4+π by positivity)]

private theorem time_bounds {x : ℝ} (hx : 100≤x) {t : ℕ} (ht : t≤medium x) :
    (t:ℝ)≤99*log x ∧ (t:ℝ)≤x^2 := by
  have p : 0<x := by linarith
  have hl : 1≤log x := by
    rw [←log_exp 1]
    apply log_le_log (exp_pos _)
    linarith [exp_one_lt_d9]
  have hcap := (show (t:ℝ)≤(medium x:ℝ) by exact_mod_cast ht).trans
    (Nat.ceil_lt_add_one (show 0≤60*log x by linarith)).le
  constructor
  · linarith
  · nlinarith [log_le_sub_one_of_pos p,mul_nonneg (show 0≤x-100 by linarith) p.le]

private theorem damping_lower {x d : ℝ} (hx : 100≤x) (hd : d≤1/100) {t : ℕ} (ht : t≤medium x) :
    1/x ≤ (1-d)^t := by
  have pos : 0<x := by linarith
  have hlog : -(1/99:ℝ) ≤ log (99/100) := by
    have h := log_le_sub_one_of_pos (show (0:ℝ)<(99/100)⁻¹ by norm_num)
    rw [log_inv] at h
    norm_num at h ⊢; linarith
  have htime := (time_bounds hx ht).1
  calc
    1/x = exp (-(log x)) := by rw [exp_neg,exp_log pos,one_div]
    _ ≤ exp ((t:ℝ)*log (99/100)) := by
      apply exp_le_exp.mpr
      nlinarith only [htime,mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)]
    _ = (99/100:ℝ)^t := by rw [Real.exp_nat_mul,exp_log (by norm_num : (0:ℝ)<99/100)]
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by linarith) _

private theorem row_update (v : EuclideanSpace ℝ (Fin N)) (t : ℕ) :
    fourthRow N (((update N)^t) v) = (1-eigen 1 (4:ZMod N))^t * fourthRow N v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ',mul_apply_eq_comp]
    change fourthRow N (((update N)^t) v-gramOp (sampledMatrix 1) (((update N)^t) v))=_
    rw [map_sub,fourthRow_gram 1 (by norm_num) (by norm_num),ih,pow_succ]
    ring

private theorem short_fit_forces_small (x c a y e : ℝ) (hx : 100≤x)
    (hc : 1/x≤c) (herr : |y-c*a|≤e) (en : e≤66/x^3) (fit : |y|≤1/x^3) : |a|≤1/x := by
  have hp : 0<x := by linarith
  have cp : 0≤c := (by positivity : 0≤1/x).trans hc
  have tr := abs_add_le y (-(y-c*a))
  have b : c*|a|≤1/x^3+66/x^3 := by
    rw [show y+ -(y-c*a)=c*a by ring,abs_mul,abs_of_nonneg cp,abs_neg] at tr
    exact tr.trans (add_le_add fit (herr.trans en))
  by_contra! gt
  have h := mul_lt_mul_of_pos_left gt (show 0<1/x by positivity)
  have l := mul_le_mul_of_nonneg_right hc (abs_nonneg a)
  have H : (1/x)*(1/x)<1/x^3+66/x^3 := h.trans_le (l.trans b)
  field_simp at H
  nlinarith

theorem ordinary_fit_forces_small (hN : 36864≤N) (ho : Odd N) (ω : CircleFlowPath.State (N^32))
    (G : GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) ω)
    (init : ‖gridR N ω‖≤(N:ℝ)^2) (h4 : eigen 1 (4:ZMod N)≤1/100)
    {t : ℕ} (ht : t≤medium N) (fit : ‖gridR N (iterate N ω t)‖≤1/(N:ℝ)^3) :
    |(CircleResidualSpectrum.initialCoeff N (N^32) (4:ZMod N) ω).re|≤1/(N:ℝ) := by
  let v := gridR N ω
  let v' := gridR N (iterate N ω t)
  let w := ((update N)^t) v
  have nn : (100:ℝ)≤N := by exact_mod_cast (show 100≤N by omega)
  have np : 0<(N:ℝ) := by linarith
  have tr := vector_tracking (by omega : 32≤N) ho ω G init t
  have hrow (a : EuclideanSpace ℝ (Fin N)) : |fourthRow N a|≤‖a‖ := by
    apply ((fourthRow N).le_opNorm a).trans
    exact (mul_le_mul_of_nonneg_right fourthRow_contract (norm_nonneg a)).trans_eq (one_mul _)
  have de := (hrow (v'-w)).trans tr
  rw [map_sub,show fourthRow N w=_ from row_update v t] at de
  have eq : (CircleResidualSpectrum.initialCoeff N (N^32) (4:ZMod N) ω).re=fourthRow N v := by
    rw [←normalizedCoeff_raw (N^32) _ ω]
    exact (fourthRow_rms _).symm
  rw [eq]
  apply short_fit_forces_small _ _ _ _ _ nn (damping_lower nn h4 ht) de _ ((hrow v').trans fit)
  calc
    _ ≤ (66/(N:ℝ)^7)*(N:ℝ)^2*(N:ℝ)^2 := mul_le_mul (mul_le_mul_of_nonneg_left init (by positivity))
      (time_bounds nn ht).2 (Nat.cast_nonneg _) (by positivity)
    _ = _ := by field_simp

private theorem screen_cost (hN : 36864≤N) (ho : Odd N) :
    (seedLaw (N^32)).real (screen N (N^32))ᶜ ≤ 1/(N:ℝ) := by
  have hp := NeZero.pos N
  have np : 0<(N:ℝ) := by exact_mod_cast hp
  have hx : (240:ℝ)≤N := by exact_mod_cast (show 240≤N by omega)
  have one : 1≤(N:ℝ) := by exact_mod_cast hp
  rw [measureReal_compl (screen_measurable _ _ (by omega) ho (by positivity)),probReal_univ]
  have r := (screen_probability N (N^32) (by omega) ho (by positivity)).1
  have nc : (N:ℝ)≤(N:ℝ)^32/240 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<240)]
    apply (mul_le_mul_of_nonneg_left hx np.le).trans
    simpa only [←sq] using (pow_le_pow_right₀ one (by decide : 2≤32))
  have e := CircleSharpEvent.exp_inverse_power np 1 (v:=(N:ℝ)^32/240)
    (by simpa using (Real.log_le_self np.le).trans nc)
  push_cast at r
  rw [show -(N:ℝ)^32/240 = -((N:ℝ)^32/240) by ring] at r
  simpa only [pow_one] using (show 1-(seedLaw (N^32)).real (screen N (N^32))≤1/(N:ℝ)^1 by linarith)

open CircleConditioning

set_option maxHeartbeats 400000 in
/-- The same Gaussian event rules out any full-grid fit by the middle cap,
including both short and middle stops, for fixed-step GD, seed-capped GD and
every valid equal-rate continuous flow. The event is Borel even though the
conclusion quantifies over all continuous times and all flow selections. -/
theorem joint_early_nonfit :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1),
    let N := n+1
    let m := N^32
    ∃ H : Set (Seed m), MeasurableSet H ∧
      (seedLaw m).real Hᶜ ≤ (25+smallBallConstant)/(N:ℝ) ∧
      ∀ ω∈H,
        (∀ t≤medium (N:ℝ), 1/(N:ℝ)^3<gridRms N m (train N m 1 (initial ω) t) ∧
          1/(N:ℝ)^3<gridRms N m (train N m (rate N m ω) (initial ω) t)) ∧
        (∀ T : ℝ, 0≤T → T≤(medium (N:ℝ):ℝ) → ∀ z : ℝ → State m, z 0=ω →
          IsFlow (circleInput N) (circleLabel N) (1/√(m:ℝ)) 1 T z →
            1/(N:ℝ)^3<‖gridR N (z T)‖) := by
  have grow : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_atTop_mono (f:=id) (fun n : ℕ => Nat.le_succ n) tendsto_id
  filter_upwards [eventually_ge_atTop 36864,feature4_second_eventually,grow.eventually fourth_eigen_lt,
    grow.eventually CircleShortFlowProjection.short_fit_forces_fourth] with n hn lower eigen flow odd
  let N := n+1
  let m := N^32
  let μ := seedLaw m
  let X (ω : Seed m) := (CircleResidualSpectrum.initialCoeff N m (4:ZMod N) ω).re
  let B := {ω : Seed m | |X ω|≤1/(N:ℝ)}
  have hp : 0<N := Nat.succ_pos _
  have nx : 0<(N:ℝ) := Nat.cast_pos.mpr hp
  have hN : 36864≤N := by dsimp [N];omega
  obtain ⟨G,_,pg,ing⟩ := CircleDiscreteMoments.design_event N 2 hN (by omega)
  obtain ⟨F,_,pf,inf⟩ := flow hp odd
  have pb : μ.real B≤smallBallConstant/(N:ℝ) := fourth_small_ball_schedule (N:=N) (by omega) lower
  have pa := screen_cost hN odd
  let A := screen N m
  let D := (Gᶜ∪Fᶜ)∪(B∪Aᶜ)
  refine ⟨(toMeasurable μ D)ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ D)ᶜ)ᶜ ≤ _
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    apply (measureReal_union_le (μ:=μ) (Gᶜ∪Fᶜ) (B∪Aᶜ)).trans
    apply (add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)).trans
    apply (add_le_add (add_le_add pg pf) (add_le_add pb pa)).trans
    have one : 1≤(N:ℝ) := by exact_mod_cast hp
    have hsq : (N:ℝ)≤(N:ℝ)^2 := (pow_one _).symm.trans_le (pow_le_pow_right₀ one (by decide : 1≤2))
    have bound : (12:ℝ)/(N:ℝ)^2≤12/N := div_le_div_of_nonneg_left (by norm_num) nx hsq
    change 12/(N:ℝ)^2+12/(N:ℝ)^2+(smallBallConstant/N+1/N) ≤ _
    exact (add_le_add (add_le_add bound bound) le_rfl).trans_eq (by ring)
  · intro ω h
    have out : ω∉D := fun hg => h (subset_toMeasurable μ D hg)
    have good : (ω∈G ∧ ω∈F) ∧ ω∉B ∧ ω∈A := by simpa [D,not_or,and_assoc] using out
    have band : ¬ |X ω|≤1/(N:ℝ) := good.2.1
    constructor
    · intro t ht
      have nfit : 1/(N:ℝ)^3<gridRms N m (train N m 1 (initial ω) t) := by
        rw [ordinary_gridRms]
        apply lt_of_not_ge
        intro fit
        exact band (ordinary_fit_forces_small hN odd ω (ing ω good.1.1).1 (ing ω good.1.1).2.2 eigen.le ht fit)
      have heq := trajectory_on_check N m _ good.2.2 (initial ω)
      refine ⟨nfit,?_⟩
      change 1/(N:ℝ)^3 < gridRms N m (train N m (capRate _) (initial ω) t)
      rw [heq]
      exact nfit
    · intro T hT hu z start Fz
      exact lt_of_not_ge (fun fit => band (inf ω good.1.2 T hT hu z start Fz fit))

/-- At least one learner attains the target RMS by the middle cap. The flow
alternative includes every admissible continuation from the same seed. -/
def earlyHit (N : ℕ) (ω : Seed (N^32)) : Prop :=
  (∃ t≤medium (N:ℝ), gridRms N (N^32) (train N (N^32) 1 (initial ω) t)≤1/(N:ℝ)^3 ∨
    gridRms N (N^32) (train N (N^32) (CircleCapMoments.rate N (N^32) ω) (initial ω) t)≤1/(N:ℝ)^3) ∨
  (∃ T : ℝ, 0≤T ∧ T≤(medium (N:ℝ):ℝ) ∧ ∃ z : ℝ → State (N^32), z 0=ω ∧
    IsFlow (circleInput N) (circleLabel N) (1/√(((N^32):ℕ):ℝ)) 1 T z ∧
      ‖gridR N (z T)‖ ≤ 1/(N:ℝ)^3)

/-- Outer probability of any early fit. In particular it also bounds the
probability for each measurable algorithm at either stated logarithmic cap. -/
theorem early_fit_probability :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), (seedLaw ((n+1)^32)).real {ω | earlyHit (n+1) ω} ≤
      (25+smallBallConstant)/((n:ℝ)+1) := by
  filter_upwards [joint_early_nonfit] with n h ho
  obtain ⟨G,_,bound,inside⟩ := h ho
  apply (measureReal_mono (s₂:=Gᶜ) ?_).trans (by simpa only [Nat.cast_succ] using bound)
  intro ω hit g
  obtain ⟨disk,flow⟩ := inside ω g
  obtain ⟨t,ht,hfixed|hcapped⟩ | ⟨T,ht,hu,z,start,isflow,fit⟩ := hit
  · exact (not_le_of_gt (disk t ht).1) hfixed
  · exact (not_le_of_gt (disk t ht).2) hcapped
  · exact (not_le_of_gt (flow T ht hu z start isflow)) fit

end CircleEarlyFit
