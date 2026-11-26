module

public import CircleVariableGD
public import CircleNarrowConditioning
import all CircleNarrowConditioning
import all CircleActualTracking
import all CircleDiscreteTracking
import all CircleKernelGD
import all CircleWidthTracking
import Mathlib.Tactic

/-! The physical residual and angular readout for an ordinary fixed learning
rate. The number of updates is rounded after division by that rate. -/
public section
noncomputable section
namespace CircleRateTrajectory
open Real MeasureTheory Set Finset CircleEscapeBridge CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleWidthTracking CircleGridSpectrum CircleSpectrum CircleKernelGD
open CircleNarrowConditioning (radius tolerance initialBound discrepancyConstant)
variable {N m : ℕ}

def horizon (η N : ℝ) := ⌈(2*π^2*N^2/η)*log (2*sqrt (12*N)*N^3)⌉₊

def rms (η : ℝ) (N : ℕ) (z : Seed m) (t : ℕ) := ‖gridR N (iterateAt N η z t)‖

def budget (η : ℝ) (N : ℕ) (z : Seed m) (t : ℕ) := η * ∑ j ∈ range t, rms η N z j

def learnerMean (η : ℝ) (N : ℕ) (z : Seed m) (t : ℕ) := CircleFlowMoments.mean (iterateAt N η z t)

theorem budget_succ (η : ℝ) (N : ℕ) (z : Seed m) (t : ℕ) :
    budget η N z (t+1)=budget η N z t+η*rms η N z t := by simp [budget,Finset.sum_range_succ,mul_add]

private theorem time {x η : ℝ} (hη : 0<η) (hx : 1≤x) :
    x^2*exp (-((η*designDecay x)*(horizon η x))) ≤ 1/x^3 := by
  have p : 0<x := by linarith
  let L := log (2*sqrt (12*x)*x^3)
  have hh : (2*π^2*x^2/η)*L≤(horizon η x:ℝ) := Nat.le_ceil _
  have logs : (5:ℝ)*log x ≤ (3/2)*L := by
    unfold L
    rw [log_mul (by positivity) (by positivity),log_mul (by norm_num) (by positivity),
      log_sqrt (by positivity),log_mul (by norm_num) p.ne',log_pow]
    norm_num
    linarith [log_nonneg hx,log_nonneg (by norm_num : (1:ℝ)≤2),log_nonneg (by norm_num : (1:ℝ)≤12)]
  have rate : 5*log x ≤ (η*designDecay x)*(horizon η x:ℝ) :=
    logs.trans ((show (3/2)*L=(η*designDecay x)*((2*π^2*x^2/η)*L) by unfold designDecay;field_simp;ring).le.trans
      (mul_le_mul_of_nonneg_left hh (by unfold designDecay;positivity)))
  have ee := exp_le_exp.mpr (neg_le_neg rate)
  rw [show exp (-(5*log x))=(x^5)⁻¹ by rw [show 5*log x=log (x^5) by rw [log_pow];norm_num,exp_neg,exp_log (by positivity)]] at ee
  exact (mul_le_mul_of_nonneg_left ee (sq_nonneg x)).trans_eq (by field_simp)

private theorem contractionAt {N : ℕ} [NeZero N] (hN : 3≤N) (ho : Odd N) {η : ℝ} (hp : 0≤η) (hi : η≤1)
    (v : EuclideanSpace ℝ (Fin N)) : ‖v-η • gramOp (sampledMatrix 1) v‖ ≤ (1-η*(1/(π*(N:ℝ))^2))*‖v‖ := by
  rw [show v-η • gramOp (sampledMatrix 1) v = (1-η) • v+η • (v-gramOp (sampledMatrix 1) v) by module]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp,abs_of_nonneg (sub_nonneg.mpr hi)]
  nlinarith only [mul_le_mul_of_nonneg_left (contraction hN ho v) hp]

private theorem run {N m : ℕ} [NeZero N] (hN : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {η ρ u R k : ℝ} (hη : 0<η) (hc : η≤1) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hk : 0<k) (hk1 : k≤1)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => k0 1) z) (start : ‖gridR N z‖≤R)
    (cash : 8/sqrt m*R≤ρ*k) (gap : 2*(30*ρ+3*u) ≤ 1/(π*(N:ℝ))^2-k) :
    ∀ t, rms η N z t≤(1-η*k)^t*R ∧ Tube ρ z (iterateAt N η z t) ∧
      ∀ s ∈ Set.Icc (0:ℝ) η, Tube ρ z (CircleDiscreteTracking.seg N (iterateAt N η z t) s) := by
  let q := 1-η*k
  let w := iterateAt N η z
  have qp : 0≤q := sub_nonneg.mpr ((mul_le_of_le_one_left hk.le hc).trans hk1)
  let P (t : ℕ) := rms η N z t≤q^t*R ∧ ∀ j, length (w t-z) j≤ρ*(1-q^t)*length z j
  have tube (t : ℕ) (H : P t) : Tube ρ z (w t) := fun j => (H.2 j).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg hρ (pow_nonneg qp t)] : ρ*(1-q^t)≤ρ) (sqrt_nonneg _))
  have next (t : ℕ) (H : P t) (s : ℝ) (hs : s∈Set.Icc (0:ℝ) η) (j : Fin m) :
      length (CircleDiscreteTracking.seg N (w t) s-z) j≤ρ*(1-q^(t+1))*length z j := by
    have mv := CircleVariableGD.move_bound (N:=N) (by omega) (tube t H) hr hs.1 j
    have d := (mul_le_mul_of_nonneg_left H.1 (show 0≤8/sqrt (m:ℝ) by positivity)).trans
      ((by ring : 8/sqrt (m:ℝ)*(q^t*R)=(8/sqrt m*R)*q^t).le.trans (mul_le_mul_of_nonneg_right cash (pow_nonneg qp t)))
    have c := mul_le_mul hs.2 (mul_le_mul_of_nonneg_right d (show 0≤length z j from sqrt_nonneg _))
      (by unfold rms length;positivity) hη.le
    exact mv.trans ((add_le_add (H.2 j) c).trans_eq (by rw [pow_succ];dsimp [q];ring))
  have along t (H : P t) s (hs : s∈Set.Icc (0:ℝ) η) : Tube ρ z (CircleDiscreteTracking.seg N (w t) s) :=
    fun j => (next t H s hs j).trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_nonneg hρ (pow_nonneg qp (t+1))] : ρ*(1-q^(t+1))≤ρ) (sqrt_nonneg _))
  have p (t : ℕ) : P t := by
    induction t with
    | zero => exact ⟨by simpa [rms,iterateAt] using start,fun j => by simp [w,iterateAt,length]⟩
    | succ t ih =>
      refine ⟨?_,next t ih η ⟨hη.le,le_rfl⟩⟩
      let v := gridR N (w t)
      let v' := gridR N (w (t+1))
      let u' := v-η • gramOp (sampledMatrix 1) v
      have defect : ‖v'-u'‖ ≤ η*(2*(30*ρ+3*u))*‖v‖ := CircleVariableGD.grid_increment hη.le
        (by omega) hm G hρ hr hu (tube t ih) (along t ih)
      have tri := norm_sub_le_norm_sub_add_norm_sub v' u' 0
      simp only [sub_zero] at tri
      have h : ‖v'‖ ≤ q*‖v‖ := tri.trans ((add_le_add defect (contractionAt hN odd hη.le hc v)).trans
        (by dsimp [q];nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gap hη.le) (norm_nonneg v)]))
      exact h.trans ((mul_le_mul_of_nonneg_left ih.1 qp).trans_eq (by ring))
  exact fun t => ⟨(p t).1,tube t (p t),along t (p t)⟩
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- On the same good initialization every endpoint has controlled energy and
path budget. The endpoint error is its measured RMS plus the kernel drift.
At the original cap the RMS even meets the tolerance divided by √N. -/
theorem trajectory (η : ℝ) (hη : 0<η) (hc : η≤1) (n : ℕ) (hN : 10000000000≤n+1) (odd : Odd (n+1)) (z : Seed ((n+1)^16))
    (G : GoodInit 1 (radius (n+1:ℕ)) (tolerance (n+1:ℕ)) (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (bound : ‖gridR (n+1) z‖ ≤ initialBound (n+1:ℕ)) :
    let N := n+1
    let H := horizon η N
    sqrt N * rms η N z H ≤ 1/(N:ℝ)^3 ∧ ∀ t, budget η N z t≤sqrt ((N^16:ℕ):ℝ) ∧
      meanEnergy (iterateAt N η z t)≤5 ∧
      |learnerMean η N z t-reference N (N^16) (weight 1 n) z| ≤ rms η N z t + discrepancyConstant/(N:ℝ)^3 := by
  intro N H
  let x : ℝ := N
  let r (t : ℕ) := gridR N (iterateAt N η z t)
  let y := learnerMean η N z
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
  obtain ⟨rp,rh,up,_,dp,dh,move,gap,area,area',cost⟩ := CircleNarrowConditioning.arithmetic big
  have hr : ρ≤1 := by linarith
  have np : 0<x := by linarith
  have Rpos : 0≤R := by dsimp [R,initialBound];positivity
  have ep : 0≤e := by dsimp [e];positivity
  have path := run (by omega : 3≤N) hm odd z hη hc rp.le hr up dp dh G bound
    (by rw [CircleNarrowConditioning.width_sqrt];exact move) gap
  have tub (t : ℕ) := (path t).2.1
  have inside (t : ℕ) := (path t).2.2
  have areaBound (t : ℕ) : budget η N z t ≤ R/d := by
    have h (k : ℕ) : d*budget η N z k+(1-η*d)^k*R ≤ R := by
      induction k with
      | zero => simp [budget]
      | succ k ih =>
        rw [budget_succ,pow_succ (1-η*d) k]
        have hb := mul_le_mul_of_nonneg_left (path k).1 (mul_nonneg hη.le dp.le)
        change η*d*rms η N z k ≤ (η*d)*((1-η*d)^k*R) at hb
        linarith only [ih,hb]
    apply (le_div_iff₀ dp).2
    linarith only [h t,mul_nonneg (pow_nonneg (sub_nonneg.mpr ((mul_le_of_le_one_left dp.le hc).trans dh)) t) Rpos]
  have Pcap (v : EuclideanSpace ℝ (Fin N)) : |P v| ≤ ‖v‖ :=
    (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_right (rowOp_norm nn zero_le_one
      (fun _ => weight_abs_le_one n 1 (by norm_num))) (norm_nonneg _)).trans_eq (one_mul _))
  have obs (t : ℕ) : |y t-P (r t)-(y 0-P (r 0))| ≤ 2*e*budget η N z t := by
    induction t with
    | zero => simp [budget]
    | succ t ih =>
      let dg := r (t+1)-(r t-η • gramOp (sampledMatrix 1) (r t))
      have grid  := CircleVariableGD.grid_increment hη.le nn hm G rp.le hr up (tub t) (inside t)
      have gd : |P dg|≤η*e*‖r t‖ := (Pcap _).trans grid
      have md := CircleVariableGD.mean_increment hη.le nn hm G rp.le hr up (tub t) (inside t)
      rw [population_row_factorization n (by omega) odd 1 (by norm_num) (by norm_num)] at md
      have yy : |y (t+1)-y t+η*P (gramOp (sampledMatrix 1) (r t))| ≤ η*e*‖r t‖ := md
      rw [show y (t+1)-P (r (t+1))-(y 0-P (r 0)) =
        (y t-P (r t)-(y 0-P (r 0)))+(y (t+1)-y t+η*P (gramOp (sampledMatrix 1) (r t)))-P dg by
          simp only [dg,map_sub,map_smul,smul_eq_mul];ring,
        budget_succ]
      exact ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ih yy)) gd)).trans_eq (by dsimp only [rms,r];ring)
  constructor
  · have runH := (path H).1.trans (mul_le_mul_of_nonneg_right (CircleKernelGD.disc_exp ((mul_le_of_le_one_left dp.le hc).trans dh) H) Rpos)
    have init : sqrt x*R≤x^2 := by unfold R initialBound; nlinarith only [sq_sqrt np.le,mul_nonneg (by linarith only [big] : 0≤x-1000) np.le]
    have w := mul_le_mul_of_nonneg_left runH (sqrt_nonneg x)
    apply w.trans
    exact (show sqrt x*(exp (-((η*d)*(H:ℝ)))*R)=exp (-((η*d)*H))*(sqrt x*R) by ring).le.trans
      ((mul_le_mul_of_nonneg_left init (exp_nonneg _)).trans ((mul_comm _ _).le.trans (time hη one)))
  · intro t
    refine ⟨(areaBound t).trans (area.trans (area'.trans_eq CircleNarrowConditioning.width_sqrt.symm)),?_,?_⟩
    · have h := CircleNarrowConditioning.energy_le (by linarith only [rp] : 0≤1+ρ) (current_length (tub t))
      have p := pow_le_pow_left₀ (by linarith only [rp] : 0≤1+ρ) (by linarith : 1+ρ≤11/10) 2
      exact h.trans ((mul_le_mul (le_refl _) G.energy (by unfold meanEnergy;positivity) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right p (by norm_num : (0:ℝ)≤4)).trans (by norm_num)))
    · rw [←actual_reference (N:=N) (by omega) z (weight 1 n)]
      change |y t-(y 0-P (r 0))| ≤ ‖r t‖+_
      rw [show y t-(y 0-P (r 0))=P (r t)+(y t-P (r t)-(y 0-P (r 0))) by ring]
      exact (abs_add_le ..).trans (add_le_add (Pcap _) ((obs t).trans
        ((mul_le_mul_of_nonneg_left (areaBound t) (by positivity)).trans cost)))


theorem budget_energy {η : ℝ} (hη : 0≤η) {N m : ℕ} (hn : 0<N) (hm : 0<m) (z : Seed m) (t : ℕ)
    (cert : budget η N z t≤sqrt m) : meanEnergy (iterateAt N η z t) ≤ (exp 8)^2*meanEnergy z := by
  let a := 8/sqrt (m:ℝ)
  have ap : 0≤a := by dsimp [a];positivity
  have mult (k : ℕ) (j : Fin m) : length (iterateAt N η z k) j ≤ exp (a*budget η N z k)*length z j := by
    induction k with
    | zero => simp [iterateAt,budget]
    | succ k ih =>
      let w := iterateAt N η z k
      have zero : Tube 0 w w := by intro j;simp [length]
      have go := CircleVariableGD.move_bound (N:=N) hn zero zero_le_one hη
      have tube : Tube (η*(a*rms η N z k)) w (CircleDiscreteTracking.seg N w η) := by
        intro j
        simpa [length,a,rms,w,mul_assoc] using go j
      have cur := current_length tube j
      have ef := add_one_le_exp (η*(a*rms η N z k))
      have first := mul_le_mul (by linarith only [ef] : 1+η*(a*rms η N z k)≤exp (η*(a*rms η N z k))) ih
        (sqrt_nonneg _) (exp_nonneg _)
      apply cur.trans (first.trans_eq ?_)
      rw [budget_succ,mul_add,exp_add,show η*(a*rms η N z k)=a*(η*rms η N z k) by ring]
      ring
  have time := (mul_le_mul_of_nonneg_left cert ap).trans_eq (show a*sqrt (m:ℝ)=8 by dsimp [a];field_simp)
  apply CircleNarrowConditioning.energy_le (exp_nonneg _)
  exact fun j => (mult t j).trans (mul_le_mul_of_nonneg_right (exp_le_exp.mpr time) (sqrt_nonneg _))


end CircleRateTrajectory
