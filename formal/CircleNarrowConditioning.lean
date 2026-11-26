module

public import CircleConditioning
public import CircleReferenceDistribution
import all CircleGDLimits
import all CircleComparison
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleConditioning
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleSharpEvent
import all CircleSharpInitialization
import all CircleCapMoments
import all CircleGaussianTracking
import all CircleKernelGD
import Mathlib.Tactic

/-! Observable endpoint certificates for ordinary unit-step descent at width
N¹⁶. The conditioning tests refer to the realised learner and its same-seed
reference. -/

public section
noncomputable section
namespace CircleNarrowConditioning
open Real MeasureTheory ProbabilityTheory Set Finset CircleEscapeBridge CircleFlowPath
  CircleTangentDrift CircleActualTracking CircleDiscreteTracking CircleGridSpectrum CircleSpectrum
  CircleKernelGD CircleCapMoments CircleGaussianTracking
variable {N m : ℕ}

def budget (N : ℕ) (z : Seed m) (t : ℕ) := ∑ j ∈ range t, ‖gridR N (iterate N z j)‖

def radius (x : ℝ) := 1000000/(x^5*sqrt x)
def tolerance (x : ℝ) := 1/x^6
def initialBound (x : ℝ) := 1000*sqrt x
def discrepancyConstant : ℝ := 2*60000006*1000*32

private theorem arithmetic {x : ℝ} (hx : 10000000000≤x) :
    0<radius x ∧ radius x ≤ 1/10 ∧ 0≤tolerance x ∧ tolerance x≤1 ∧
      0<designDecay x ∧ designDecay x≤1 ∧
      8/x^8 * initialBound x ≤ radius x*designDecay x ∧
      2*(30*radius x+3*tolerance x) ≤ 1/(π*x)^2-designDecay x ∧
      initialBound x/designDecay x ≤ 32000*x^2*sqrt x ∧
      32000*x^2*sqrt x ≤ x^8 ∧
      2*(2*(30*radius x+3*tolerance x))*(initialBound x/designDecay x) ≤ discrepancyConstant/x^3 := by
  have p : 0<x := by linarith
  have o : 1≤x := by linarith
  have a : 1≤sqrt x := by simpa using sqrt_le_sqrt o
  have a' : sqrt x ≤ x := (sqrt_le_iff).mpr ⟨p.le,by nlinarith [mul_nonneg (sub_nonneg.mpr o) p.le]⟩
  have s := sq_sqrt p.le
  have pp := pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2
  have pl := one_le_pow₀ (by linarith [pi_gt_three] : 1 ≤ π) (n:=2)
  have large (k : ℕ) (hk : 1≤k) : x≤x^k := by simpa using pow_le_pow_right₀ o hk
  have rp : 0<radius x := by unfold radius; positivity
  have rh : radius x≤1/10 := by
    unfold radius;rw [div_le_div_iff₀ (by positivity) (by norm_num)];nlinarith [le_mul_of_one_le_right (pow_nonneg p.le 5) a,large 5 (by decide)]
  have kp : 0<designDecay x := by unfold designDecay;positivity
  have k1 : designDecay x≤1 := by unfold designDecay; rw [div_le_one (by positivity)];nlinarith [one_le_mul_of_one_le_of_one_le pl (one_le_pow₀ o (n:=2))]
  have small : tolerance x ≤ 1/(x^5*sqrt x) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact (mul_le_mul_of_nonneg_left a' (pow_nonneg p.le 5)).trans_eq (by ring)
  have e : 2*(30*radius x+3*tolerance x) ≤ 60000006/(x^5*sqrt x) := by
    unfold radius;calc
      _ ≤ 2*(30*(1000000/(x^5*sqrt x))+3*(1/(x^5*sqrt x))) := by gcongr
      _ = _ := by ring
  have B : initialBound x/designDecay x ≤ 32000*x^2*sqrt x := by
    unfold initialBound designDecay; field_simp; nlinarith only [pp]
  refine ⟨rp,rh,by unfold tolerance; positivity,by unfold tolerance;exact (div_le_one (by positivity)).mpr (one_le_pow₀ o),
    kp,k1,?_,e.trans ?_,B,?_,?_⟩
  · unfold radius initialBound designDecay
    field_simp
    rw [s]; nlinarith only [mul_le_mul_of_nonneg_right pp p.le,p.le]
  · have hh : 240000024*π^2 ≤ x^3*sqrt x := by
      nlinarith [large 3 (by decide),le_mul_of_one_le_right (pow_nonneg p.le 3) a]
    unfold designDecay
    rw [show 1/(π*x)^2-3/(4*π^2*x^2)=1/(4*π^2*x^2) by field_simp;ring,div_le_div_iff₀ (by positivity) (by positivity)]
    exact (show 60000006*(4*π^2*x^2) = (240000024*π^2)*x^2 by ring).le.trans
      ((mul_le_mul_of_nonneg_right hh (sq_nonneg x)).trans_eq (by ring))
  · calc
      _ ≤ 32000*x^2*x := mul_le_mul_of_nonneg_left a' (by positivity)
      _ ≤ x^5*x^3 := by nlinarith only [mul_le_mul_of_nonneg_right ((by linarith only [hx] : (32000:ℝ)≤x).trans (large 5 (by decide))) (pow_nonneg p.le 3)]
      _ = _ := by ring
  · have h := mul_le_mul (mul_le_mul_of_nonneg_left e (by norm_num : (0:ℝ)≤2)) B
      (div_nonneg (by unfold initialBound;positivity) kp.le) (by positivity)
    exact h.trans_eq (by unfold discrepancyConstant;field_simp;ring)

private theorem width_sqrt {N : ℕ} : sqrt ((N^16:ℕ):ℝ)=(N:ℝ)^8 := by
  push_cast; rw [show (N:ℝ)^16=((N:ℝ)^8)^2 by ring,sqrt_sq (by positivity)]

/-- A single Gaussian event controls both kernel blocks, both classes of
gate margins, initial energy and initial grid residual at the narrower width. -/
theorem gaussian_event (N : ℕ) [NeZero N] (hN : 10000000000≤N) :
    ∃ G : Set (Seed (N^16)), MeasurableSet G ∧ (seedLaw (N^16)).real Gᶜ ≤ 12/(N:ℝ)^98 ∧
    ∀ z ∈ G, GoodInit 1 (radius N) (tolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z ∧
      ‖gridR N z‖ ≤ initialBound N := by
  have hn : 0<N := by omega
  have p : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have one : (1:ℝ)≤N := by exact_mod_cast hn
  have large : (10000000000:ℝ)≤N := by exact_mod_cast hN
  obtain ⟨rp,rh,up,uh,_⟩ := arithmetic large
  let I := {z : Seed (N^16) | ¬GoodInit 1 (radius N) (tolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z}
  let R := {z : Seed (N^16) | 2+64*sqrt (((98:ℝ)+1)*log N) < CircleGaussianTracking.initialRms N (N^16) z}
  let μ := seedLaw (N^16)
  have i := CircleGaussianBernstein.goodInit_exponential (N:=N) (pow_pos hn 16) (τ:=1)
    (by norm_num) rp.le (by linarith : radius N≤1) up uh
  have eq : -((N^16:ℕ):ℝ)*(tolerance N)^2/36864 = -((N:ℝ)^4/36864) := by unfold tolerance;push_cast;field_simp
  rw [eq] at i
  have cost := CircleSharpEvent.log_cost N 100 (by omega) hn
  have power : (N:ℝ)^2≤(N:ℝ)^4/36864 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<36864)]
    have x : (36864:ℝ)≤(N:ℝ)^2 := (by linarith only [large] : 36864≤(N:ℝ)).trans (by simpa using pow_le_pow_right₀ one (by decide : 1≤2))
    exact (mul_le_mul_of_nonneg_left x (sq_nonneg _)).trans_eq (by ring)
  have ex := CircleSharpEvent.exp_inverse_power p 100 (cost.trans power)
  have hb : ((N:ℝ)+1)^2+1 ≤ 5*(N:ℝ)^2 := by nlinarith [sq_nonneg ((N:ℝ)-1)]
  have fi : μ.real I ≤ 10/(N:ℝ)^98 := i.trans ((mul_le_mul hb (mul_le_mul_of_nonneg_left ex (by norm_num))
    (by positivity) (by positivity)).trans_eq (by field_simp;ring))
  have fr : μ.real R ≤ 2/(N:ℝ)^98 := by
    apply CircleSharpInitialization.initialRms_polynomial hn (pow_pos hn 16) 98
    push_cast
    have h := CircleSharpEvent.log_cost N 99 (by omega) hn
    norm_num at h ⊢
    nlinarith only [h,pow_le_pow_right₀ one (by decide : 2≤16)]
  refine ⟨(toMeasurable μ (I∪R))ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    exact ((measureReal_union_le _ _).trans (add_le_add fi fr)).trans_eq (by ring)
  · intro z hz
    have q : z∉I∪R := fun h => hz (subset_toMeasurable _ _ h)
    have u : z∉I ∧ z∉R := by simpa only [Set.mem_union,not_or] using q
    have h : ‖gridR N z‖ ≤ 2+64*sqrt (((98:ℝ)+1)*log N) := le_of_not_gt u.2
    have v : sqrt (((98:ℝ)+1)*log N) ≤ 10*sqrt N := by
      apply (sqrt_le_iff).mpr ⟨by positivity,?_⟩
      rw [mul_pow,sq_sqrt p.le];nlinarith [log_le_self p.le]
    exact ⟨not_not.mp u.1,h.trans (by unfold initialBound;nlinarith [show 1≤sqrt (N:ℝ) by simpa using sqrt_le_sqrt one])⟩


private theorem energy_le {z w : Seed m} {a : ℝ} (_ha : 0≤a)
    (h : ∀ j, length w j ≤ a*length z j) : meanEnergy w ≤ a^2*meanEnergy z := by
  unfold meanEnergy
  rw [←mul_div_assoc,Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun j _ => (pow_le_pow_left₀ (sqrt_nonneg _) (h j) 2).trans_eq (mul_pow ..)

private theorem energy_eq (z : Seed m) : meanEnergy z = CircleCapInduction.energy (initial z) := by
  rw [CircleCapInduction.energy,initial_energy_coordinates,meanEnergy,Fintype.sum_prod_type]
  simp [length_sq,Fin.sum_univ_three,add_assoc]

def learnerMean (N : ℕ) (z : Seed m) (t : ℕ) := CircleFlowMoments.mean (iterate N z t)

def rms (N : ℕ) (z : Seed m) (t : ℕ) := ‖gridR N (iterate N z t)‖

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- On the same good initialization every endpoint has controlled energy and
path budget. The endpoint error is its measured RMS plus the kernel drift.
At the original cap the RMS even meets the tolerance divided by √N. -/
theorem trajectory (n : ℕ) (hN : 10000000000≤n+1) (odd : Odd (n+1)) (z : Seed ((n+1)^16))
    (G : GoodInit 1 (radius (n+1:ℕ)) (tolerance (n+1:ℕ)) (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (bound : ‖gridR (n+1) z‖ ≤ initialBound (n+1:ℕ)) :
    let N := n+1
    let H := CircleFlowTracking.horizon N
    sqrt N * rms N z H ≤ 1/(N:ℝ)^3 ∧ ∀ t, budget N z t≤sqrt ((N^16:ℕ):ℝ) ∧
      meanEnergy (iterate N z t)≤5 ∧
      |learnerMean N z t-reference N (N^16) (weight 1 n) z| ≤ rms N z t + discrepancyConstant/(N:ℝ)^3 := by
  intro N H
  let x : ℝ := N
  let r (t : ℕ) := gridR N (iterate N z t)
  let y := learnerMean N z
  let P := rowOp (fun _ : Fin N => weight 1 n)
  let d := designDecay x
  let ρ := radius x
  let u := tolerance x
  let e := 2*(30*ρ+3*u)
  let R := initialBound x
  have big : 10000000000≤x := by dsimp only [x];exact_mod_cast hN
  have one : 1≤x := by linarith
  have nn : 0<N := Nat.succ_pos _
  have hm := pow_pos nn 16
  obtain ⟨rp,rh,up,_,dp,dh,move,gap,area,area',cost⟩ := arithmetic big
  have hr : ρ≤1 := by linarith
  have np : 0<x := by linarith
  have Rpos : 0≤R := by dsimp [R,initialBound];positivity
  have ep : 0≤e := by dsimp [e];positivity
  have run := discrete_bootstrap nn hm G rp.le hr up dp dh bound
    (by rw [width_sqrt];exact move)
    (fun v => (contraction (N:=N) (by omega) odd v).trans
      (mul_le_mul_of_nonneg_right (by linarith only [gap]) (norm_nonneg _)))
  have tub (t : ℕ) : Tube ρ z (iterate N z t) := fun j => ((run t).2 j).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg rp.le (pow_nonneg (sub_nonneg.mpr dh) t)] :
      ρ*(1-(1-designDecay x)^t) ≤ ρ) (sqrt_nonneg _))
  have inside (t : ℕ) (s : ℝ) (hs : s∈Set.Icc 0 1) := CircleDiscreteTracking.tube_segment (tub t) (tub (t+1)) hs
  have areaBound (t : ℕ) : budget N z t ≤ R/d := by
    have h (k : ℕ) : d*budget N z k+(1-d)^k*R ≤ R := by
      induction k with
      | zero => simp [budget]
      | succ k ih =>
        rw [show budget N z (k+1)=budget N z k+‖r k‖ by simp [budget,r,Finset.sum_range_succ],pow_succ (1-d) k]
        linarith only [ih,mul_le_mul_of_nonneg_left (run k).1 dp.le]
    apply (le_div_iff₀ dp).2
    linarith only [h t,mul_nonneg (pow_nonneg (sub_nonneg.mpr dh) t) Rpos]
  have Pcap (v : EuclideanSpace ℝ (Fin N)) : |P v| ≤ ‖v‖ :=
    (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_right (rowOp_norm nn zero_le_one
      (fun _ => weight_abs_le_one n 1 (by norm_num))) (norm_nonneg _)).trans_eq (one_mul _))
  have obs (t : ℕ) : |y t-P (r t)-(y 0-P (r 0))| ≤ 2*e*budget N z t := by
    induction t with
    | zero => simp [budget]
    | succ t ih =>
      let dg := r (t+1)-(r t-gramOp (sampledMatrix 1) (r t))
      have grid := grid_increment nn hm G rp.le hr up (tub t) (inside t)
      have gd : |P dg|≤e*‖r t‖ := (Pcap _).trans grid
      have md := mean_increment nn hm G rp.le hr up (tub t) (inside t)
      rw [population_row_factorization n (by omega) odd 1 (by norm_num) (by norm_num)] at md
      have yy : |y (t+1)-y t+P (gramOp (sampledMatrix 1) (r t))| ≤ e*‖r t‖ := md
      rw [show y (t+1)-P (r (t+1))-(y 0-P (r 0)) =
        (y t-P (r t)-(y 0-P (r 0)))+(y (t+1)-y t+P (gramOp (sampledMatrix 1) (r t)))-P dg by
          simp only [dg,map_sub];ring,
        show budget N z (t+1)=budget N z t+‖r t‖ by simp [budget,r,Finset.sum_range_succ]]
      exact ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ih yy)) gd)).trans_eq (by ring)
  constructor
  · have runH := (run H).1.trans (mul_le_mul_of_nonneg_right (CircleKernelGD.disc_exp dh H) Rpos)
    have init : sqrt x*R≤x^2 := by unfold R initialBound; nlinarith only [sq_sqrt np.le,mul_nonneg (by linarith only [big] : 0≤x-1000) np.le]
    have w := mul_le_mul_of_nonneg_left runH (sqrt_nonneg x)
    apply w.trans
    exact (show sqrt x*(exp (-(d*(H:ℝ)))*R)=exp (-(d*H))*(sqrt x*R) by ring).le.trans
      ((mul_le_mul_of_nonneg_left init (exp_nonneg _)).trans ((mul_comm _ _).le.trans (design_time one)))
  · intro t
    refine ⟨(areaBound t).trans (area.trans (area'.trans_eq width_sqrt.symm)),?_,?_⟩
    · have h := energy_le (by linarith only [rp] : 0≤1+ρ) (current_length (tub t))
      have p := pow_le_pow_left₀ (by linarith only [rp] : 0≤1+ρ) (by linarith : 1+ρ≤11/10) 2
      exact h.trans ((mul_le_mul (le_refl _) G.energy (by unfold meanEnergy;positivity) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right p (by norm_num : (0:ℝ)≤4)).trans (by norm_num)))
    · rw [←actual_reference (N:=N) (by omega) z (weight 1 n)]
      change |y t-(y 0-P (r 0))| ≤ ‖r t‖+_
      rw [show y t-(y 0-P (r 0))=P (r t)+(y t-P (r t)-(y 0-P (r 0))) by ring]
      exact (abs_add_le ..).trans (add_le_add (Pcap _) ((obs t).trans
        ((mul_le_mul_of_nonneg_left (areaBound t) (by positivity)).trans cost)))


private theorem budget_energy {N m : ℕ} (hn : 0<N) (hm : 0<m) (z : Seed m) (t : ℕ)
    (cert : budget N z t≤sqrt m) : meanEnergy (iterate N z t) ≤ (exp 8)^2*meanEnergy z := by
  let a := 8/sqrt (m:ℝ)
  have ap : 0≤a := by dsimp [a];positivity
  have mult (k : ℕ) (j : Fin m) : length (iterate N z k) j ≤ exp (a*budget N z k)*length z j := by
    induction k with
    | zero => simp [iterate,budget]
    | succ k ih =>
      let w := iterate N z k
      have zero : Tube 0 w w := by intro j;simp [length]
      have go := CircleDiscreteTracking.move_bound (N:=N) hn zero zero_le_one 1 ⟨zero_le_one,le_rfl⟩
      have tube : Tube (a*‖gridR N w‖) w (seg N w 1) := by
        intro j
        simpa [length,a] using go j
      have cur := current_length tube j
      have ef := add_one_le_exp (a*‖gridR N w‖)
      have first := mul_le_mul (by linarith only [ef] : 1+a*‖gridR N w‖≤exp (a*‖gridR N w‖)) ih
        (sqrt_nonneg _) (exp_nonneg _)
      apply cur.trans (first.trans_eq ?_)
      rw [show budget N z (k+1)=budget N z k+‖gridR N w‖ by simp [budget,w,Finset.sum_range_succ],mul_add,exp_add]
      ring
  have time := (mul_le_mul_of_nonneg_left cert ap).trans_eq (show a*sqrt (m:ℝ)=8 by dsimp [a];field_simp)
  apply energy_le (exp_nonneg _)
  exact fun j => (mult t j).trans (mul_le_mul_of_nonneg_right (exp_le_exp.mpr time) (sqrt_nonneg _))

private theorem meas_rms (N m t : ℕ) : Measurable (fun z : Seed m => rms N z t) := by
  have h := (CircleConditioning.random_rate_statistics N m (fun _ => 1) measurable_const t).1
  simpa only [CircleConditioning.ordinary_gridRms,rms] using h

private theorem mean_eq (N : ℕ) (z : Seed m) (t : ℕ) :
    learnerMean N z t = trainedMean (CircleSeedIntegrability.path N m 1) t z :=
  congrArg (CircleEscape.populationMean (1/sqrt (m:ℝ))) (iterate_eq_train N z t)

private theorem meas_mean (N m t : ℕ) : Measurable (fun z : Seed m => learnerMean N z t) := by
  simpa only [mean_eq,trainedMean,CircleSeedIntegrability.path] using (CircleConditioning.random_rate_statistics N m (fun _ => 1) measurable_const t).2

private theorem meas_energy (N m t : ℕ) : Measurable (fun z : Seed m => meanEnergy (iterate N z t)) := by
  simp only [energy_eq,iterate_eq_train,CircleCapInduction.energy,CircleCapInduction.rawEnergy]
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro j _
  have h := CircleConditioning.random_rate_parameters N m (fun _ => 1) measurable_const t j
  exact (h.1.pow_const 2).add (h.2.norm.pow_const 2)

private theorem meas_budget (N m t : ℕ) : Measurable (fun z : Seed m => budget N z t) :=
  Finset.measurable_fun_sum _ (fun j _ => meas_rms N m j)

private theorem meas_stop {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {f : Ω → ℕ → E} {t : Ω→ℕ} (mt : Measurable t) (mf : ∀ n, Measurable (fun z => f z n)) :
    Measurable (fun z => f z (t z)) :=
  (measurable_from_prod_countable_left (f:=fun p : Ω × ℕ => f p.1 p.2) mf).comp
    (measurable_id.prodMk mt)

private def filled {Ω : Type*} (A : Set Ω) (Y : Ω → ℝ) (z : Ω) : ℝ :=
  @ite _ (z∈A) (Classical.propDecidable _) (Y z) 1

private theorem filled_meas {Ω : Type*} [MeasurableSpace Ω] {A : Set Ω} {Y : Ω→ℝ}
    (ma : MeasurableSet A) (my : Measurable Y) : Measurable (filled A Y) := by
  classical
  exact my.piecewise ma measurable_const

def envelopeConstant : ℝ := 10+2*(exp 8)^2

/-- Fourth moment on any measurable observable certificate, including rare
fits outside the initialization event. Either the returned energy or the
entire cumulative residual can certify an individual fit. -/
private theorem exceptional {N m : ℕ} (hn : 0<N) (hm : 0<m) (t : Seed m → ℕ) (mt : Measurable t)
    {A : Set (Seed m)} (ma : MeasurableSet A)
    (guard : ∀ z ∈ A, meanEnergy (iterate N z (t z))≤5 ∨ budget N z (t z)≤sqrt m)
    (b : ℝ) (hb : 0≤b) (hb' : b≤1) (G : Set (Seed m)) :
    let D := fun z => filled A (fun w => learnerMean N w (t w)) z-reference N m b z
    Integrable (fun z => (D z)^2) (seedLaw m) ∧
      (∫ z in G, (D z)^2 ∂seedLaw m) ≤ (100*envelopeConstant^2)*m*sqrt ((seedLaw m).real G) := by
  intro D
  have md : Measurable D := (filled_meas ma (meas_stop mt (meas_mean N m))).sub (reference_measurable N m b)
  have c : 0<envelopeConstant := by unfold envelopeConstant;positivity
  have env : ∀ᵐ z ∂seedLaw m, |D z/envelopeConstant| ≤ sqrt m*(CircleCapInduction.energy (initial z)+1)/2 := by
    filter_upwards with z
    let E := CircleCapInduction.energy (initial z)
    have en : 0≤E := by change 0≤CircleCapInduction.energy (initial z);rw [←energy_eq];unfold meanEnergy;positivity
    have root : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
    have re := reference_envelope N m hn hm b hb hb' z
    change |reference N m b z| ≤ 1+sqrt m*E at re
    rw [abs_div,abs_of_pos c,div_le_iff₀ c]
    by_cases h : z∈A
    · have actual := mean_le_energy m hm (initial (iterate N z (t z)))
      change |learnerMean N z (t z)|≤sqrt m*CircleCapInduction.energy (initial (iterate N z (t z)))/2 at actual
      rw [←energy_eq] at actual
      have bnd : meanEnergy (iterate N z (t z)) ≤ 5+(exp 8)^2*E := by
        rcases guard z h with h'|h'
        · exact h'.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) en))
        · exact (budget_energy hn hm z _ h').trans (by rw [energy_eq];linarith)
      have f := (mul_le_mul_of_nonneg_left bnd (sqrt_nonneg (m:ℝ)))
      simp only [D,filled,ite_eq_left h]
      apply (abs_sub ..).trans ((add_le_add actual re).trans ?_)
      change _≤sqrt m*(E+1)/2*envelopeConstant
      unfold envelopeConstant
      nlinarith only [f,root,mul_nonneg (sqrt_nonneg (m:ℝ)) en,
        mul_nonneg (sqrt_nonneg (m:ℝ)) (sq_nonneg (exp 8)),
        mul_nonneg (mul_nonneg (sqrt_nonneg (m:ℝ)) en) (sq_nonneg (exp 8))]
    · simp only [D,filled,ite_eq_right h]
      apply (abs_sub ..).trans ((add_le_add (le_refl _) re).trans ?_)
      change |(1:ℝ)| + (1+sqrt m*E) ≤ sqrt m*(E+1)/2*envelopeConstant
      rw [abs_one];unfold envelopeConstant
      nlinarith only [root,mul_nonneg (sqrt_nonneg (m:ℝ)) en,
        mul_nonneg (sqrt_nonneg (m:ℝ)) (sq_nonneg (exp 8)),
        mul_nonneg (mul_nonneg (sqrt_nonneg (m:ℝ)) en) (sq_nonneg (exp 8))]
  obtain ⟨i,bound⟩ := CircleCapMoments.envelope_fourth m hm _ (md.div_const _) env
  have eq (z) : (D z)^4 = envelopeConstant^4*(D z/envelopeConstant)^4 := by field_simp
  have four : Integrable (fun z => (D z)^4) (seedLaw m) := by simp_rw [eq];exact i.const_mul _
  have mem : MemLp (fun z => (D z)^2) 2 (seedLaw m) :=
    (memLp_two_iff_integrable_sq (md.pow_const 2).aestronglyMeasurable).2 (by simpa only [←pow_mul] using four)
  refine ⟨mem.integrable one_le_two,(CircleMoment.exceptional_second_moment mem G).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
  apply (sqrt_le_left (by positivity)).mpr
  simp_rw [eq]; rw [integral_const_mul,gaussian_eighth] at *
  exact (mul_le_mul_of_nonneg_left bound (pow_nonneg c.le 4)).trans (by
    nlinarith only [mul_nonneg (pow_nonneg c.le 4) (sq_nonneg (m:ℝ))])


inductive FitTest | rms | maxResidual
inductive Endpoint | cap | firstHit
inductive Certificate | budget | energy | either

def trainingResidual (N : ℕ) (z : Seed m) (t : ℕ) (i : Fin N) : ℝ :=
  CircleEscape.output (1/sqrt m) (CircleInitializationCheck.train N m 1 (initial z) t)
    (CircleEscape.gridPoint N i) - (1+(CircleEscape.gridPoint N i).re)

def hits (test : FitTest) (N : ℕ) (z : Seed m) (t : ℕ) : Prop :=
  match test with
  | .rms => rms N z t ≤ 1/(N:ℝ)^3
  | .maxResidual => ∀ i, |trainingResidual N z t i| ≤ 1/(N:ℝ)^3

def returned (stop : Endpoint) (test : FitTest) (N : ℕ) (z : Seed m) : ℕ :=
  match stop with
  | .cap => CircleFlowTracking.horizon N
  | .firstHit => @CircleConditioning.firstHit (CircleFlowTracking.horizon N) (hits test N z) (Classical.decPred _)

def certified (cert : Certificate) (N : ℕ) (z : Seed m) (t : ℕ) : Prop :=
  match cert with
  | .budget => budget N z t ≤ sqrt m
  | .energy => meanEnergy (iterate N z t) ≤ 5
  | .either => budget N z t ≤ sqrt m ∨ meanEnergy (iterate N z t) ≤ 5

def accepted (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) : Set (Seed m) :=
  {z | hits test N z (returned stop test N z) ∧ certified cert N z (returned stop test N z)}

private theorem rms_sq (N : ℕ) (z : Seed m) (t : ℕ) :
    (rms N z t)^2 = (∑ i, (trainingResidual N z t i)^2)/N := by
  rw [rms,←CircleConditioning.ordinary_gridRms,CircleConditioning.gridRms,sq_sqrt (by positivity)]
  rfl

private theorem hit_sandwich (test : FitTest) {N : ℕ} (hn : 0<N) (z : Seed m) (t : ℕ) :
    (sqrt N*rms N z t ≤ 1/(N:ℝ)^3 → hits test N z t) ∧
      (hits test N z t → rms N z t ≤ 1/(N:ℝ)^3) := by
  have mp : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have sq := rms_sq N z t
  have all : (∑ i, (trainingResidual N z t i)^2)=(N:ℝ)*(rms N z t)^2 :=
    (by have h := (eq_div_iff mp.ne').mp sq;linarith)
  have non : 0≤rms N z t := norm_nonneg _
  cases test with
  | rms =>
    exact ⟨fun h => (le_mul_of_one_le_left non (one_le_sqrt.mpr (by exact_mod_cast hn))).trans h,id⟩
  | maxResidual =>
    constructor
    · intro h i
      apply le_trans _ h
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (sqrt_nonneg _) non)).mp
      rw [sq_abs,mul_pow,sq_sqrt mp.le,←all]
      exact Finset.single_le_sum (f:=fun i => trainingResidual N z t i ^2) (fun _ _ => sq_nonneg _) (mem_univ i)
    · intro h
      apply (sq_le_sq₀ non (by positivity)).mp
      rw [sq,div_le_iff₀ mp]
      have hsum := Finset.sum_le_sum (s:=univ) (g:=fun _ : Fin N => (1/(N:ℝ)^3)^2)
        (fun i _ => (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (h i) 2))
      simpa [mul_comm] using hsum

private theorem meas_hit (test : FitTest) (N m : ℕ) (t : Seed m→ℕ) (mt : Measurable t) :
    MeasurableSet {z | hits test N z (t z)} := by
  classical
  cases test with
  | rms => exact measurableSet_le (meas_stop mt (meas_rms N m)) measurable_const
  | maxResidual =>
    change MeasurableSet {z : Seed m | ∀ i, |trainingResidual N z (t z) i| ≤ 1/(N:ℝ)^3}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    apply continuous_abs.measurable.comp
    apply meas_stop (f:=fun z t => trainingResidual N z t i) mt
    intro k
    let u := fun z : Seed m => CircleInitializationCheck.train N m 1 (initial z) k
    have h := CircleConditioning.random_rate_parameters N m (fun _ => 1) measurable_const k
    exact (CircleSeedIntegrability.output_meas u (fun j => (h j).1) (fun j => (h j).2) _ _).sub measurable_const

private theorem meas_returned (stop : Endpoint) (test : FitTest) (N m : ℕ) :
    Measurable (returned (m:=m) stop test N) := by
  classical
  cases stop with
  | cap => exact measurable_const
  | firstHit =>
    apply CircleConditioning.firstHit_measurable
    exact fun t => meas_hit test N m (fun _ => t) measurable_const

theorem measurable_accepted (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) :
    MeasurableSet (accepted stop test cert N m) := by
  let t := returned (m:=m) stop test N
  have mt := meas_returned stop test N m
  have a := meas_hit test N m t mt
  have eb := measurableSet_le (meas_stop mt (meas_energy N m)) (measurable_const (a:=(5:ℝ)))
  have bb := measurableSet_le (meas_stop mt (meas_budget N m)) (measurable_const (a:=sqrt (m:ℝ)))
  cases cert with
  | budget => exact a.inter bb
  | energy => exact a.inter eb
  | either => exact a.inter (bb.union eb)

def completedMean (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) :=
  filled (accepted stop test cert N m) (fun z => learnerMean N z (returned stop test N z))

def mseConstant := 2*((1+discrepancyConstant)^2+400*envelopeConstant^2)

/-- Conditional paired second moment at width N¹⁶ with actual Gaussian
initialization, actual unit steps and the archived horizon. All combinations
of fixed cap or first hit, RMS or max-residual fit, and either observable
certificate are covered. -/
theorem conditional_mse (n : ℕ) (hN : 10000000000≤n+1) (odd : Odd (n+1))
    (stop : Endpoint) (test : FitTest) (cert : Certificate) :
    let N := n+1
    let m := N^16
    let μ := seedLaw m
    let A := accepted stop test cert N m
    let t := returned (m:=m) stop test N
    1-12/(N:ℝ)^98 ≤ μ.real A ∧
      MemLp (completedMean stop test cert N m) 2 μ ∧
      (∫ z, (completedMean stop test cert N m z-reference N m (weight 1 n) z)^2 ∂μ) ≤ mseConstant/(N:ℝ)^6 ∧
      (∫ z, (learnerMean N z (t z)-reference N m (weight 1 n) z)^2 ∂cond μ A) ≤ mseConstant/(N:ℝ)^6 := by
  classical
  intro N m μ A t
  have nn : 0<N := Nat.succ_pos _
  have hm : 0<m := pow_pos nn _
  have np : (0:ℝ)<N := Nat.cast_pos.mpr nn
  have one : (1:ℝ)≤N := by exact_mod_cast nn
  have large : (10000000000:ℝ)≤N := by exact_mod_cast hN
  have ma := measurable_accepted stop test cert N m
  have mt := meas_returned stop test N m
  obtain ⟨G,mg,pr,good⟩ := gaussian_event N hN
  let Y := fun z => learnerMean N z (t z)-reference N m (weight 1 n) z
  let W := completedMean stop test cert N m
  let D := fun z => W z-reference N m (weight 1 n) z
  have cap (z : Seed m) (hz : z∈G) := trajectory n hN odd z (good z hz).1 (good z hz).2
  have gh (z : Seed m) (hz : z∈G) : hits test N z (t z) := by
    have Hcap := (hit_sandwich test nn z _).1 (cap z hz).1
    cases stop with
    | cap => exact Hcap
    | firstHit =>
      apply (@CircleConditioning.firstHit_spec (CircleFlowTracking.horizon N) (hits test N z) _).2.1.mpr
      exact ⟨_,le_rfl,Hcap⟩
  have ga : G⊆A := by
    intro z hz
    refine ⟨gh z hz,?_⟩
    have h := (cap z hz).2 (t z)
    cases cert with
    | budget => exact h.1
    | energy => exact h.2.1
    | either => exact Or.inl h.1
  have prA : 1-12/(N:ℝ)^98 ≤ μ.real A := by
    have h := measureReal_mono (μ:=μ) ga
    have pr' : μ.real Gᶜ ≤ 12/(N:ℝ)^98 := pr
    rw [measureReal_compl mg,probReal_univ] at pr'
    linarith
  have guard (z : Seed m) (hz : z∈A) : meanEnergy (iterate N z (t z))≤5 ∨ budget N z (t z)≤sqrt m := by
    have h := hz.2
    cases cert with
    | budget => exact Or.inr h
    | energy => exact Or.inl h
    | either => exact h.symm
  have wt := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  obtain ⟨inte,tail⟩ := exceptional nn hm t mt ma guard (weight 1 n) wt.1 wt.2 Gᶜ
  change Integrable (fun z => (D z)^2) μ at inte
  change (∫ z in Gᶜ, (D z)^2 ∂μ) ≤ 100*envelopeConstant^2*(m:ℝ)*sqrt (μ.real Gᶜ) at tail
  have root : sqrt (μ.real Gᶜ) ≤ 4/(N:ℝ)^49 := by
    apply (sqrt_le_iff).mpr ⟨by positivity,pr.trans ?_⟩
    rw [div_pow,←pow_mul];norm_num;gcongr;norm_num
  have bad := tail.trans (mul_le_mul_of_nonneg_left root (by positivity))
  have small : 100*envelopeConstant^2*(m:ℝ)*(4/(N:ℝ)^49) ≤ 400*envelopeConstant^2/(N:ℝ)^6 := by
    dsimp only [m];push_cast
    calc
      _ = 400*envelopeConstant^2/(N:ℝ)^33 := by field_simp;ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ one (by decide : 6≤33))
  let B := (1+discrepancyConstant)/(N:ℝ)^3
  have val (z) (hz : z∈G) : |D z|≤B := by
    have h : z∈accepted stop test cert N m := ga hz
    simp only [D,W,completedMean,filled,ite_eq_left h]
    apply ((cap z hz).2 (t z)).2.2.trans
    calc
      _ ≤ 1/(N:ℝ)^3+discrepancyConstant/(N:ℝ)^3 := add_le_add ((hit_sandwich test nn z (t z)).2 (gh z hz)) le_rfl
      _ = B := by unfold B;ring
  have goodInt : (∫ z in G, (D z)^2 ∂μ) ≤ B^2 := by
    have bound := setIntegral_mono_on inte.integrableOn (integrable_const (B^2)) mg (fun z hz =>
      (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (val z hz) 2))
    exact bound.trans (by rw [setIntegral_const,smul_eq_mul];exact (mul_le_mul_of_nonneg_right (measureReal_le_one (μ:=μ) (s:=G)) (sq_nonneg B)).trans_eq (one_mul _))
  let C := (1+discrepancyConstant)^2+400*envelopeConstant^2
  have all : (∫ z, (D z)^2 ∂μ) ≤ C/(N:ℝ)^6 := by
    rw [←integral_add_compl mg inte]
    exact (add_le_add goodInt (bad.trans small)).trans_eq (by dsimp [B,C];ring)
  have half : 1/2 ≤ μ.real A := by
    have ge : (24:ℝ) ≤ (N:ℝ)^98 := (by linarith only [large] : 24≤(N:ℝ)).trans (by simpa using pow_le_pow_right₀ one (by decide : 1≤98))
    have le : 12/(N:ℝ)^98 ≤1/2 := (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
    linarith only [prA,le]
  have cp : 0≤C/(N:ℝ)^6 := by dsimp [C];positivity
  have wm : Measurable W := filled_meas ma (meas_stop mt (meas_mean N m))
  have zm := CircleSeedIntegrability.reference_memLp N m (weight 1 n) 2 (by norm_num)
  have dm : MemLp D 2 μ := (memLp_two_iff_integrable_sq (wm.sub (reference_measurable N m (weight 1 n))).aestronglyMeasurable).2 inte
  have wl : MemLp W 2 μ := by
    have h := dm.add zm
    simpa only [Pi.add_def,D,sub_add_cancel] using h
  have eq : (∫ z in A, (Y z)^2 ∂μ) = ∫ z in A, (D z)^2 ∂μ := by
    apply setIntegral_congr_fun ma
    intro z hz
    change z∈accepted stop test cert N m at hz
    simp only [D,W,completedMean,filled,ite_eq_left hz,Y,t]
  have on := eq.le.trans ((setIntegral_le_integral inte (ae_of_all _ fun z => sq_nonneg (D z))).trans all)
  refine ⟨prA,wl,all.trans (by change C/(N:ℝ)^6≤2*C/(N:ℝ)^6;linarith only [cp,show 2*C/(N:ℝ)^6=2*(C/(N:ℝ)^6) by ring]),?_⟩
  change (∫ z, (Y z)^2 ∂cond μ A) ≤ _
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,←div_eq_inv_mul]
  apply (div_le_iff₀ (by change 0<μ.real A;linarith only [half])).mpr
  apply on.trans
  change C/(N:ℝ)^6 ≤ (2*C/(N:ℝ)^6)*μ.real A
  nlinarith only [mul_le_mul_of_nonneg_left half cp, show 2*C/(N:ℝ)^6*(μ.real A) =2*(C/(N:ℝ)^6)*(μ.real A) by ring]


private theorem centered_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A : Set Ω}
    (ma : MeasurableSet A) (Y g : Ω → ℝ) (f : ℝ→ℝ) (h : f 1=0) (same : g=filled A Y) :
    (∫ z, f (Y z) ∂cond μ A)=(∫ z, f (g z) ∂μ)/μ.real A := by
  classical
  have eq : (fun z => f (g z)) = A.indicator (fun z => f (Y z)) := by
    funext z
    by_cases hz : z∈A <;> simp [same,filled,hz,h]
  rw [eq,integral_indicator ma,ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = _ / (μ A).toReal
  ring

open Filter Topology

set_option maxHeartbeats 900000 in
/-- The fit-conditioned signed bias and variance at width N¹⁶ converge to
the original Gaussian-reference constants after either observable trajectory
certificate. The scope includes the weaker disjunction of the two checks. -/
theorem conditional_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 10000000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (stop : Endpoint) (test : FitTest) (cert : Certificate) :
    let N := fun i => n i+1
    let m := fun i => (N i)^16
    let ν := fun i => cond (seedLaw (m i)) (accepted stop test cert (N i) (m i))
    let Y := fun i (z : Seed (m i)) => learnerMean (N i) z (returned stop test (N i) z)
    Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ z, Y i z ∂ν i)-1)) atTop (𝓝 (-(π^2/36))) ∧
      Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (ν i)) atTop (𝓝 (7*π^2/1620)) := by
  intro N m ν Y
  let x (i : ℕ) := (n i:ℝ)+1
  let μ (i : ℕ) := seedLaw (m i)
  let A (i : ℕ) := accepted stop test cert (N i) (m i)
  let W (i : ℕ) := completedMean stop test cert (N i) (m i)
  let b := -(π^2/36)
  let v := 7*π^2/1620
  let p (i : ℕ) := (μ i).real (A i)
  have ma (i : ℕ) : MeasurableSet (A i) := measurable_accepted .. 
  have data (i : ℕ) := conditional_mse (n i) (hn i) (odd i) stop test cert
  have prob (i : ℕ) : 1-12/(x i)^98≤p i := by
    simpa only [x,Nat.cast_add,Nat.cast_one] using (data i).1
  have wm (i : ℕ) : MemLp (W i) 2 (μ i) := (data i).2.1
  have cpos : 0≤mseConstant := by unfold mseConstant;positivity
  have all := CircleComparison.gaussian_reference_transfer n m grow (fun i => by have := hn i;omega)
    odd (fun i => pow_pos (Nat.succ_pos _) _) (τ:=1) (by norm_num) W wm
    (CircleGDLimits.scaled_rms n grow cpos (fun i => by
      simpa only [Nat.cast_add,Nat.cast_one] using (data i).2.2.1))
  have fullBias : Tendsto (fun i => (x i)^2*((∫ z, W i z ∂μ i)-1)) atTop (𝓝 b) := by
    convert all.1.neg using 2 with i <;> dsimp [x,b,μ] <;> ring
  have fullVar : Tendsto (fun i => (x i)^4*ProbabilityTheory.variance (W i) (μ i)) atTop (𝓝 v) := by
    convert all.2 using 2; ring
  have nz (i : ℕ) : μ i (A i)≠0 := by
    intro h
    have hp : p i=0 := by change (μ i (A i)).toReal=0;rw [h,ENNReal.toReal_zero]
    have one : 1≤x i := by dsimp [x];linarith only [Nat.cast_nonneg (α:=ℝ) (n i)]
    have hi : 10000000000≤x i := by dsimp [x];exact_mod_cast hn i
    have pos : 12/(x i)^98 < 1 := (div_lt_one (by positivity)).mpr ((by linarith only [hi] : (12:ℝ)<x i).trans_le
      (by simpa using pow_le_pow_right₀ one (by decide : 1≤98)))
    linarith only [prob i,hp,pos]
  let probLaw (i : ℕ) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (nz i)
  have ym (i : ℕ) : MemLp (Y i) 2 (ν i) := by
    have wi : MemLp (W i) 2 (ν i) := ((wm i).restrict (s:=A i)).smul_measure (by simpa using nz i)
    apply wi.ae_eq
    apply Measure.ae_smul_measure
    apply (ae_restrict_iff' (ma i)).mpr
    exact ae_of_all _ fun z hz => by change filled (A i) (Y i) z=Y i z;simp [filled,hz]
  have pl : Tendsto p atTop (𝓝 1) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow).pow 98
    have lo : Tendsto (fun i => 1-12/(x i)^98) atTop (𝓝 1) := by
      simpa [x,div_pow,div_eq_mul_inv] using (tendsto_const_nhds (x:=(1:ℝ))).sub (h.const_mul 12)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le lo tendsto_const_nhds prob (fun _ => measureReal_le_one)
  have fullRisk : Tendsto (fun i => (x i)^4*∫ z, (W i z-1)^2 ∂μ i) atTop (𝓝 (v+b^2)) := by
    convert fullVar.add (fullBias.pow 2) using 2 with i
    rw [CircleStats.mse_decomposition (wm i) 1];ring
  have bias : Tendsto (fun i => (x i)^2*((∫ z, Y i z ∂ν i)-1)) atTop (𝓝 b) := by
    convert fullBias.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := centered_integral (μ i) (ma i) (Y i) (W i) (fun y => y-1) (by norm_num) rfl
      change (∫ z, Y i z-1 ∂ν i) = (∫ z, W i z-1 ∂μ i)/p i at h
      rw [integral_sub ((ym i).integrable one_le_two) (integrable_const _),
        integral_sub ((wm i).integrable one_le_two) (integrable_const _),integral_const,integral_const,
        probReal_univ,probReal_univ,one_smul] at h
      rw [h,Pi.div_apply];ring
    · ring
  have risk : Tendsto (fun i => (x i)^4*∫ z, (Y i z-1)^2 ∂ν i) atTop (𝓝 (v+b^2)) := by
    convert fullRisk.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := centered_integral (μ i) (ma i) (Y i) (W i) (fun y => (y-1)^2) (by norm_num) rfl
      change (∫ z, (Y i z-1)^2 ∂ν i) = (∫ z, (W i z-1)^2 ∂μ i)/p i at h
      rw [h,Pi.div_apply];ring
    · ring
  refine ⟨bias,?_⟩
  convert risk.sub (bias.pow 2) using 2 with i
  · rw [CircleStats.mse_decomposition (ym i) 1];ring
  · ring

end CircleNarrowConditioning
