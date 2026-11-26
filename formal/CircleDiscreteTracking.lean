module

public import CircleSharpInitialization
public import CircleKernelGD
public import CircleGaussianBernstein
public import CircleSharpTracking
public import CircleCapMoments
import all CircleSeedIntegrability
import all CircleKernelGD
import all CircleActualTracking
import all CircleTangentDrift
import all CircleFlowPath
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationCheck
import all CircleMeanDynamics
import all CircleFlowMoments
import Mathlib.Tactic

/-! Simultaneous unit-step GD at the initial grid gates. Segment integration
uses the frozen update velocity, including across zero preactivations. -/
public section
noncomputable section
namespace CircleDiscreteTracking
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking
variable {N m : ℕ}

def direction (N : ℕ) (z : State m) : State m :=
  velocity 1 (fun i => row (1/sqrt m) z (circleInput N i) (startGates z i))
    (residual (circleInput N) (circleLabel N) (1/sqrt m) z)

def seg (N : ℕ) (z : State m) (s : ℝ) : State m := fun p => z p+s*direction N z p

def iterate (N : ℕ) (z : State m) : ℕ → State m
  | 0 => z
  | t+1 => seg N (iterate N z t) 1

private theorem pre_complex (z : State m) (j : Fin m) (x : ℂ) :
    inner ℝ ((CircleEscapeBridge.initial z).w j) x = pre z j (x.re,x.im) := by
  simp [CircleEscapeBridge.initial,Complex.inner,Complex.mul_re,pre]

private theorem output_complex (z : State m) (x : ℂ) (c : ℝ) :
    CircleEscape.output c (CircleEscapeBridge.initial z) x = output c z (x.re,x.im) := by
  simp only [CircleEscape.output,CircleEscape.feature,pre_complex,output]; rfl

/-- The Cartesian simultaneous update represented by a segment is exactly the
original complex-weight learner, for every seed including grid kinks. -/
theorem step_eq (N : ℕ) (z : State m) :
    CircleEscapeBridge.initial (seg N z 1) = CircleEscape.step (CircleEscape.gridPoint N)
      (fun i => 1+(CircleEscape.gridPoint N i).re) (1/sqrt m) (1/(N*sqrt m)) (CircleEscapeBridge.initial z) := by
  let a := residual (circleInput N) (circleLabel N) (1/sqrt m) z
  have rr (i : Fin N) : CircleEscape.output (1/sqrt m) (CircleEscapeBridge.initial z) (CircleEscape.gridPoint N i) -
      (1+(CircleEscape.gridPoint N i).re) = a i := by rw [output_complex]; rfl
  have pp (i : Fin N) (j : Fin m) : inner ℝ ((CircleEscapeBridge.initial z).w j) (CircleEscape.gridPoint N i) =
      pre z j (circleInput N i) := pre_complex _ _ _
  simp only [CircleEscape.step,rr,CircleEscape.feature,CircleEscape.gate,pp]
  unfold CircleEscapeBridge.initial
  congr 1
  · ext j
    change z (j,0)+1*direction N z (j,0) = z (j,0) - _*_
    simp only [direction,velocity,gradient,rate,row, ↓reduceIte, Matrix.cons_val_zero, one_mul]
    change z (j,0) + -(1:ℝ)*((1/N)*∑ i, a i * ((1/sqrt m)*max (pre z j (circleInput N i)) 0)) = _
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul,Finset.mul_sum,← Finset.sum_neg_distrib,sub_eq_add_neg,neg_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros; ring
  · funext j
    apply Complex.ext
    all_goals
      simp only [Complex.sub_re,Complex.sub_im,Complex.real_smul,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_sum,Complex.im_sum,
        zero_mul,sub_zero,add_zero,seg,one_mul,direction,velocity,gradient,rate,row,
        startGates,actualGate,Matrix.cons_val_one,Matrix.cons_val_zero,Fin.isValue]
    all_goals
      simp only [show (1:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 0 by decide, ↓reduceIte,
        ← sub_eq_add_neg,neg_mul,one_mul,div_eq_mul_inv,mul_inv_rev]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a,circleInput]
      ring

theorem iterate_eq_train (N : ℕ) (z : State m) (T : ℕ) :
    CircleEscapeBridge.initial (iterate N z T) =
      CircleInitializationCheck.train N m 1 (CircleEscapeBridge.initial z) T := by
  induction T with
  | zero => rfl
  | succ t ih => rw [iterate,CircleInitializationCheck.train,step_eq,ih]

private theorem seg_ac (N : ℕ) (z : State m) (p : Coord m) :
    AbsolutelyContinuousOnInterval (fun s => seg N z s p) 0 1 :=
  (show ContDiff ℝ 1 (fun s => z p+s*direction N z p) by fun_prop).contDiffOn.absolutelyContinuousOnInterval

private theorem seg_deriv (N : ℕ) (z : State m) (p : Coord m) (s : ℝ) :
    HasDerivAt (fun s => seg N z s p) (direction N z p) s := by
  simpa only [seg,id_eq,one_mul] using ((hasDerivAt_id s).mul_const (direction N z p)).const_add (z p)

private theorem mixed_contraction (z v : State m) (x : ℝ × ℝ) (s : Fin m → ℝ) :
    pair (row (1/sqrt m) z x s) (direction N v) =
      -rowOp (fun i => entry 1 z v x (circleInput N i) s (startGates v i)) (gridR N v) := by
  rw [gridR,rowOp_rms]
  simp only [entry,pair,direction,velocity,gradient, Finset.mul_sum,Finset.sum_mul,
    div_eq_mul_inv,←Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Mixed Jacobian row along the open or closed parameter segment. -/
def mixedRow (N : ℕ) (z : State m) (x : ℝ × ℝ) (s : ℝ) (i : Fin N) :=
  entry 1 (seg N z s) z x (circleInput N i)
    (fun j => actualGate (pre (seg N z s) j x)) (startGates z i)

private theorem observable_deriv (N : ℕ) (z : State m) (x : ℝ × ℝ) :
    ∀ᵐ s : ℝ, s ∈ uIcc 0 1 → HasDerivAt (fun t => output (1/sqrt m) (seg N z t) x)
      (-(rowOp (mixedRow N z x s) (gridR N z))) s := by
  have hk : ∀ᵐ s, ∀ j : Fin m, s ∈ uIcc 0 1 →
      DifferentiableAt ℝ (fun t => max (pre (seg N z t) j x) 0) s :=
    ae_all_iff.mpr fun j => (CircleFlowPath.acfeature (seg_ac N z) j x).ae_differentiableAt
  filter_upwards [hk] with s hs H
  have h := output_deriv (c:=1/sqrt m) (fun p => seg_deriv N z p s) (fun j => hs j H)
    (fun j => actualGate (pre (seg N z s) j x)) (fun _ => actualGate_admissible _)
  rw [mixed_contraction] at h
  exact h

/-- A frozen tangent row approximates an actual prediction increment whenever
every mixed row on the simultaneous update segment has the indicated entry error. -/
theorem increment {x : ℝ × ℝ} (hn : 0<N) (z : State m) (k : Fin N → ℝ) {e : ℝ} (he : 0 ≤ e)
    (close : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, |mixedRow N z x s i - k i| ≤ e) :
    |output (1/sqrt m) (seg N z 1) x-output (1/sqrt m) z x+rowOp k (gridR N z)| ≤ e*‖gridR N z‖ := by
  let b := rowOp k (gridR N z)
  let y := fun s => output (1/sqrt m) (seg N z s) x + s*b
  have ac : AbsolutelyContinuousOnInterval y 0 1 :=
    (output_ac (seg_ac N z) _ x).fun_add
      ((show ContDiff ℝ 1 (fun s : ℝ => s*b) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 1 → |deriv y s| ≤ e * ‖gridR N z‖ := by
    filter_upwards [observable_deriv N z x] with s hs H
    have hs' := hs (mem_uIcc_of_le H.1.le H.2)
    have h := hs'.add ((hasDerivAt_id s).mul_const b)
    change HasDerivAt y _ s at h
    rw [h.deriv,one_mul,neg_add_eq_sub]
    have norm := (rowOp_norm hn he (fun i => by simpa [abs_sub_comm] using close s ⟨H.1.le,H.2⟩ i))
    have hl := ((rowOp (k-mixedRow N z x s)).le_opNorm (gridR N z)).trans
      (mul_le_mul_of_nonneg_right norm (norm_nonneg _))
    simpa only [b,Real.norm_eq_abs,rowOp_sub,sub_apply] using hl
  have h := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    (by norm_num) ac intervalIntegrable_const bound
  have z0 : seg N z 0 = z := by ext; simp [seg]
  simpa [y,z0,b,add_sub_right_comm] using h


private theorem grid_close {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) (i : Fin N) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ j, |mixedRow N z (circleInput N i) s j - K i j| ≤ 2*(30*ρ+3*u) := by
  intro s hs j
  apply two_rate_budget hρ hr G.energy (G.gridMargin i) (G.gridMargin j) _ (G.gram i j)
  exact entry_drift hm (by norm_num) (by norm_num) hρ (grid_unit i) (grid_unit j) (along s hs) tz
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)

/-- Exact simultaneous update compared with one discrete kernel Euler step. -/
theorem grid_increment {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) :
    ‖gridR N (seg N z 1) - (gridR N z - gramOp K (gridR N z))‖ ≤ 2*(30*ρ+3*u)*‖gridR N z‖ := by
  let r := gridR N z
  let a (i : Fin N) := output (1/sqrt m) (seg N z 1) (circleInput N i) -
    output (1/sqrt m) z (circleInput N i) + rowOp (K i) r
  have eq : gridR N (seg N z 1)-(r - gramOp K r) = rmsCoordinates a := by
    ext i
    change (output (1/sqrt m) (seg N z 1) (circleInput N i)-circleLabel N i)/sqrt N -
      ((output (1/sqrt m) z (circleInput N i)-circleLabel N i)/sqrt N - gramOp K r i) = a i/sqrt N
    dsimp only [a]
    rw [gramOp_apply,rowOp_apply]
    generalize (output (1/sqrt m) (seg N z 1) (circleInput N i)) = x
    generalize (output (1/sqrt m) z (circleInput N i)) = y
    generalize circleLabel N i = h
    generalize (∑ j, K i j * r.ofLp j) = b
    have ns := sq_sqrt (Nat.cast_nonneg N)
    generalize sqrt (N:ℝ) = d at *
    have dpos : d≠0 := by intro h; rw [h] at ns; have hNreal : (0:ℝ)<N := Nat.cast_pos.mpr hn; nlinarith
    field_simp
    nlinarith only [congrArg (fun t : ℝ => b*t) ns]
  rw [eq, ←Real.sqrt_sq (norm_nonneg _),rmsCoordinates_norm_sq]
  apply (sqrt_le_iff).2 ⟨by positivity,?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  have hb (i : Fin N) : |a i| ≤ 2*(30*ρ+3*u)*‖r‖ :=
    increment hn z (K i) (by positivity) (grid_close hm G hρ hr tz along i)
  refine (Finset.sum_le_sum (g:=fun _ => (2*(30*ρ+3*u)*‖r‖)^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  · simp [mul_comm,r]

private def mixedMean (N : ℕ) (z : State m) (s : ℝ) (i : Fin N) :=
  meanEntry 1 (seg N z s) z (circleInput N i) (startGates z i)

private theorem mean_contraction (hm : 0 < m) (z : State m) (s : ℝ) :
    (∫ v, pair (row (1/sqrt m) (seg N z s) (phase v) (fun j =>
        CircleMeanDynamics.gate (seg N z s) j v)) (direction N z) ∂angularLaw) =
      -rowOp (mixedMean N z s) (gridR N z) := by
  let a := residual (circleInput N) (circleLabel N) (1/sqrt m) z
  simp_rw [mixed_contraction,gridR,rowOp_rms]
  rw [integral_neg,integral_div]
  have hi (i : Fin N) : Integrable (fun v => angleEntry 1 (seg N z s) z
      (circleInput N i) (startGates z i) v*a i) angularLaw :=
    (angleEntry_integrable hm _ _ _ _ _).mul_const _
  change -((∫ v, ∑ i, angleEntry 1 (seg N z s) z (circleInput N i) (startGates z i) v*a i ∂angularLaw)/N) = _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_const]
  rfl

/-- The actual angular population mean over a unit GD update obeys the mixed
tangent-row approximation, including through zero hidden weights. -/
theorem mean_increment {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) :
    |CircleFlowMoments.mean (seg N z 1)-CircleFlowMoments.mean z+rowOp kQ (gridR N z)| ≤
      2*(30*ρ+3*u)*‖gridR N z‖ := by
  let W := seg N z
  let b := rowOp kQ (gridR N z)
  let y (s : ℝ) := CircleFlowMoments.mean (W s)+s*b
  have mac : AbsolutelyContinuousOnInterval (fun s => CircleFlowMoments.mean (W s)) 0 1 := by
    simp_rw [CircleMeanDynamics.mean_as_sum]
    exact (acsum Finset.univ _ (fun (j : Fin m) _ => (seg_ac N z (j,0)).fun_mul
      (CircleMeanDynamics.feature_ac (seg_ac N z) j))).const_mul _
  have ac : AbsolutelyContinuousOnInterval y 0 1 := mac.fun_add
    ((show ContDiff ℝ 1 (fun s : ℝ => s*b) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)
  have hreg : ∀ᵐ s, ∀ j, s ∈ uIcc 0 1 →
      DifferentiableAt ℝ (fun t => CircleMeanDynamics.meanFeature (W t) j) s :=
    ae_all_iff.mpr fun j => (CircleMeanDynamics.feature_ac (seg_ac N z) j).ae_differentiableAt
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 1 → |deriv y s| ≤ 2*(30*ρ+3*u)*‖gridR N z‖ := by
    filter_upwards [hreg] with s hs H
    have hp (p : Coord m) := seg_deriv N z p s
    have dh := (HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      (hp (j,0)).mul (CircleMeanDynamics.feature_deriv hp j (hs j (mem_uIcc_of_le H.1.le H.2))))).const_mul (1/sqrt m)
    have md : HasDerivAt (fun t => CircleFlowMoments.mean (W t)) (-rowOp (mixedMean N z s) (gridR N z)) s := by
      simp_rw [CircleMeanDynamics.mean_as_sum]
      apply dh.congr_deriv
      rw [← mean_contraction hm, CircleMeanDynamics.integrated_row]
    have h := md.add ((hasDerivAt_id s).mul_const b)
    change HasDerivAt y _ s at h
    rw [h.deriv,one_mul,neg_add_eq_sub]
    have close (i : Fin N) : |kQ i - mixedMean N z s i| ≤ 2*(30*ρ+3*u) := by
      rw [abs_sub_comm]
      exact two_rate_budget hρ hr G.energy G.angular (G.gridMargin i)
        (angular_entry_drift hm (by norm_num) (by norm_num : |(1:ℝ)|≤2) hρ (grid_unit i)
          (along s ⟨H.1.le,H.2⟩) tz (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)) (G.mean i)
    have h := ((rowOp (kQ-mixedMean N z s)).le_opNorm (gridR N z)).trans
      (mul_le_mul_of_nonneg_right (rowOp_norm hn (by positivity) close) (norm_nonneg _))
    simpa only [b,Real.norm_eq_abs,rowOp_sub,sub_apply] using h
  have h := CircleSharpTracking.endpoint_variation (C:=2*(30*ρ+3*u)) (q:=fun _ => ‖gridR N z‖)
    (by norm_num) ac intervalIntegrable_const bound
  have z0 : W 0 = z := by ext; simp [W,seg]
  simpa [y,z0,W,b,add_sub_right_comm,show seg N z 0=z from z0] using h

private theorem move_bound {z₀ z : State m} {ρ : ℝ} (hn : 0<N) (tz : Tube ρ z₀ z)
    (hr : ρ≤1) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : Fin m) :
    length (seg N z s - z₀) j ≤ length (z-z₀) j + (8/sqrt m)*‖gridR N z‖ * length z₀ j := by
  let d := (2/sqrt m)*‖gridR N z‖*length z j
  have dpos : 0≤d := by dsimp [d]; have := sqrt_nonneg (∑ k, z (j,k)^2); unfold length; positivity
  have ht (k : Fin 3) : |(seg N z s - z) (j,k)| ≤ d := by
    change |z (j,k)+s*direction N z (j,k)-z (j,k)| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul hs.2 (coordinate_speed z _ _ hn (by norm_num : |(1:ℝ)|≤2) (startGates_admissible z) j k)
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  have hδ : length (seg N z s-z) j ≤ 2*d := by
    apply (sqrt_le_iff).2 ⟨by positivity,?_⟩
    apply (Finset.sum_le_sum (g:=fun _ => d^2) (fun k _ => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ht k) 2)).trans
    simp; nlinarith [sq_nonneg d]
  let a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => seg N z s (j,k))
  let b : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => z (j,k))
  let c : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => z₀ (j,k))
  have htri : length (seg N z s-z₀) j ≤ length (seg N z s-z) j + length (z-z₀) j := by
    simp only [CircleActualTracking.length_entity]
    exact norm_sub_le_norm_sub_add_norm_sub a b c
  have hcur := (CircleActualTracking.current_length tz j).trans
    (mul_le_mul_of_nonneg_right (by linarith : 1+ρ≤2) (sqrt_nonneg _))
  have hscale : 2*d ≤ 8/sqrt m*‖gridR N z‖*length z₀ j := by
    have hh := mul_le_mul_of_nonneg_left hcur (show 0≤(2/sqrt m)*‖gridR N z‖ by positivity)
    exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  linarith

/-- Bootstrap for the actual GD sequence. A segment is confined before its
mixed kernel is used for contraction. Radius and constants are common to
every iteration and the initial lengths may vanish. -/
theorem discrete_bootstrap {ρ u R k : ℝ} {z₀ : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (_hk : 0<k) (hk1 : k≤1) (R0 : ‖gridR N z₀‖ ≤ R)
    (budget : 8/sqrt m * R ≤ ρ*k)
    (linear : ∀ r : EuclideanSpace ℝ (Fin N), ‖r - gramOp K r‖ ≤ (1-k-2*(30*ρ+3*u))*‖r‖) :
    ∀ t, ‖gridR N (iterate N z₀ t)‖ ≤ (1-k)^t*R ∧
      ∀ j, length (iterate N z₀ t-z₀) j ≤ ρ*(1-(1-k)^t)*length z₀ j := by
  let q := 1-k
  have hq : 0≤q := by dsimp [q];linarith
  intro t
  induction t with
  | zero =>
    constructor
    · simpa [iterate] using R0
    · intro j; simp [iterate,length]
  | succ t ih =>
    let z := iterate N z₀ t
    have cur : Tube ρ z₀ z := by
      intro j
      exact (ih.2 j).trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hρ (pow_nonneg hq t)] : ρ*(1-q^t) ≤ ρ) (sqrt_nonneg _))
    have step (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (j : Fin m) :
        length (seg N z s-z₀) j ≤ ρ*(1-q^(t+1))*length z₀ j := by
      have hm' := move_bound (N:=N) hn cur hr s hs j
      have dn : 8/sqrt m*‖gridR N z‖ ≤ ρ*k*q^t := by
        have h := mul_le_mul_of_nonneg_left ih.1 (show 0≤8/sqrt (m:ℝ) by positivity)
        exact h.trans ((by ring : 8/sqrt (m:ℝ)*((1-k)^t*R)=(8/sqrt m*R)*q^t) ▸
          (mul_le_mul_of_nonneg_right budget (pow_nonneg hq t)))
      apply hm'.trans ((add_le_add (ih.2 j) (mul_le_mul_of_nonneg_right dn (sqrt_nonneg _))).trans_eq ?_)
      simp only [pow_succ]; dsimp [q,length]; ring
    have along (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : Tube ρ z₀ (seg N z s) := fun j =>
      (step s hs j).trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hρ (pow_nonneg hq (t+1))] : ρ*(1-q^(t+1)) ≤ ρ) (sqrt_nonneg _))
    refine ⟨?_,step 1 ⟨zero_le_one,le_rfl⟩⟩
    have de := grid_increment hn hm G hρ hr hu cur along
    have contracted : ‖gridR N (seg N z 1)‖ ≤ q*‖gridR N z‖ := by
      have h := linear (gridR N z)
      have tri' := norm_sub_le_norm_sub_add_norm_sub (gridR N (seg N z 1)) (gridR N z-gramOp K (gridR N z)) 0
      simp only [sub_zero] at tri'
      dsimp [q]; linarith
    exact contracted.trans ((mul_le_mul_of_nonneg_left ih.1 hq).trans_eq (by dsimp [q];ring))


private theorem tube_segment {z₀ z : State m} {ρ : ℝ} (h : Tube ρ z₀ z) (h' : Tube ρ z₀ (seg N z 1))
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : Tube ρ z₀ (seg N z s) := by
  intro j
  let a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => (z-z₀) (j,k))
  let b : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => (seg N z 1-z₀) (j,k))
  have eq : (WithLp.toLp 2 (fun k => (seg N z s-z₀) (j,k)) : EuclideanSpace ℝ (Fin 3)) =
      (1-s) • a+s • b := by ext k; change z (j,k)+s*direction N z (j,k)-z₀ (j,k) =
        (1-s)*(z (j,k)-z₀ (j,k))+s*(z (j,k)+1*direction N z (j,k)-z₀ (j,k)); ring
  rw [CircleActualTracking.length_entity,eq]
  have ha : ‖a‖ ≤ ρ*length z₀ j := by simpa only [CircleActualTracking.length_entity] using h j
  have hb : ‖b‖ ≤ ρ*length z₀ j := by simpa only [CircleActualTracking.length_entity] using h' j
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hs.1,abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact (add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hs.2)) (mul_le_mul_of_nonneg_left hb hs.1)).trans_eq (by ring)

open CircleGridSpectrum CircleKernelGD CircleSpectrum CircleEscapeBridge

/-- Original width, unit step and full grid. Every nonlinear iterate contracts,
the prescribed horizon fits to N⁻³, and both the grid and angular observables
satisfy simultaneous kernel error estimates throughout the actual trajectory. -/
theorem design_trajectory [NeZero N] (hN : 32 ≤ N) (odd : Odd N) (z : State (N^32))
    (G : GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z)
    (R0 : ‖gridR N z‖ ≤ (N:ℝ)^2) :
    let r := fun t => gridR N (iterate N z t)
    let f := fun t => CircleFlowMoments.mean (iterate N z t)
    (∀ t, ‖r t‖ ≤ (1-designDecay N)^t*‖r 0‖) ∧ ‖r (CircleFlowTracking.horizon N)‖ ≤ 1/(N:ℝ)^3 ∧
      (∀ t, ‖r (t+1)-(r t-gramOp (sampledMatrix 1) (r t))‖ ≤ (66/(N:ℝ)^7)*‖r t‖) ∧
      ∀ t, |f (t+1)-f t+rowOp (fun _ => k0 1) (r t)| ≤ (66/(N:ℝ)^7)*‖r t‖ := by
  intro r f
  have hreal : (32:ℝ) ≤ N := by exact_mod_cast hN
  have npos : (0:ℝ)<N := by linarith
  have hn : 0 < N := by omega
  have hm := pow_pos hn 32
  have width : sqrt ((N^32:ℕ):ℝ)=(N:ℝ)^16 := by
    push_cast; rw [show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have hk : 0 < designDecay N := by unfold designDecay;positivity
  have hk1 : designDecay N ≤ 1 := by
    unfold designDecay; rw [div_le_one (by positivity)]
    have p : 1 ≤ π^2 := one_le_pow₀ (by linarith [pi_gt_three])
    have n : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ (by linarith)
    nlinarith [one_le_mul_of_one_le_of_one_le p n]
  have hρ : 0 ≤ designRadius N := by unfold designRadius; positivity
  have hu : 0 ≤ designTolerance N := by unfold designTolerance; positivity
  obtain ⟨hr,he,hgap,hbud⟩ := design_bounds hreal
  have bud : 8/sqrt ((N^32:ℕ):ℝ)*‖gridR N z‖ ≤ designRadius N*designDecay N := by
    rw [width]
    apply (mul_le_mul_of_nonneg_left R0 (by positivity : (0:ℝ)≤8/(N:ℝ)^16)).trans
    have h := ((div_lt_iff₀ (mul_pos (by positivity) hk)).mp hbud).le
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    linarith
  have lin (v : EuclideanSpace ℝ (Fin N)) := (contraction (by omega : 3≤N) odd v).trans
    (mul_le_mul_of_nonneg_right (by linarith : 1-1/(π*(N:ℝ))^2 ≤
      1-designDecay N-2*(30*designRadius N+3*designTolerance N)) (norm_nonneg _))
  have run := discrete_bootstrap hn hm G hρ hr hu hk hk1 (le_rfl (a:=‖gridR N z‖)) bud lin
  have tube (t : ℕ) : Tube (designRadius N) z (iterate N z t) := fun j =>
    ((run t).2 j).trans (mul_le_mul_of_nonneg_right (by
      nlinarith [mul_nonneg hρ (pow_nonneg (sub_nonneg.mpr hk1) t)] :
      designRadius N*(1-(1-designDecay N)^t) ≤ designRadius N) (sqrt_nonneg _))
  have along (t : ℕ) (s : ℝ) (hs : s∈Icc 0 1) := tube_segment (tube t) (tube (t+1)) hs
  refine ⟨fun t => (run t).1,?_,fun t => (grid_increment hn hm G hρ hr hu (tube t) (along t)).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)),fun t => (mean_increment hn hm G hρ hr hu (tube t) (along t)).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg _))⟩
  apply ((run _).1.trans (mul_le_mul (CircleKernelGD.disc_exp hk1 _) R0 (norm_nonneg _) (exp_nonneg _))).trans
  rw [mul_comm]
  exact design_time (by linarith)

set_option maxHeartbeats 750000 in
/-- Exact constant-mode proxy after finite stopping. The discrepancy from
the true learner accumulates the two actual one-step defects and the scalar
constant-row error. -/
private theorem endpoint_bounds (n : ℕ) (hN : 32 ≤ n+1) (odd : Odd (n+1)) (z : State ((n+1)^32))
    (G : GoodInit 1 (designRadius (n+1)) (designTolerance (n+1))
      (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (R0 : ‖gridR (n+1) z‖ ≤ ((n:ℝ)+1)^2) (T : ℕ) :
    let N := n+1
    let b := weight 1 n
    let a := 1-gamma N
    |trainedMean (CircleSeedIntegrability.path N (N^32) 1) T z -
      reference N (N^32) (b*(1-a^T)) z| ≤ 3*(66/(N:ℝ)^7)*‖gridR N z‖*T ∧
    |trainedMean (CircleSeedIntegrability.path N (N^32) 1) T z-reference N (N^32) b z| ≤
      ‖gridR N (iterate N z T)‖+2*(66/(N:ℝ)^7)*‖gridR N z‖*T := by
  intro N b a
  let r := fun t => gridR N (iterate N z t)
  let f := fun t => CircleFlowMoments.mean (iterate N z t)
  let P := rowOp (fun _ : Fin N => b)
  let e := 66/(N:ℝ)^7
  let U := e*‖r 0‖
  have hn : 0<N := by dsimp [N]; omega
  have D := design_trajectory hN odd z (by simpa [N] using G) (by simpa [N] using R0)
  have apos : 0≤ a := sub_nonneg.mpr (gamma_bounds (N:=N)).2
  have a1 : a ≤ 1 := sub_le_self _ ((show (0:ℝ)≤3/π^2 by positivity).trans (gamma_bounds (N:=N)).1)
  have epos : 0≤e := by dsimp [e]; positivity
  have hk : 0 ≤ designDecay N := by unfold designDecay; positivity
  have hk1 : designDecay N≤1 := by
    have h : (32:ℝ)≤N := by exact_mod_cast hN
    unfold designDecay; rw [div_le_one (by positivity)]
    nlinarith [one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [pi_gt_three] : 1≤π) (n:=2))
      (one_le_pow₀ (by linarith : (1:ℝ)≤N) (n:=2))]
  have rb (t : ℕ) : ‖r t‖ ≤ ‖r 0‖ := by
    apply (D.1 t).trans
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (sub_nonneg.mpr hk1) (sub_le_self _ hk)) (norm_nonneg _)).trans_eq (one_mul _)
  have pb (v : EuclideanSpace ℝ (Fin N)) : |P v| ≤ ‖v‖ :=
    (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_right
      (rowOp_norm hn zero_le_one (fun _ => weight_abs_le_one n 1 (by norm_num))) (norm_nonneg v)).trans_eq (one_mul _))
  have pnorm (t : ℕ) : |P (r (t+1)) - a*P (r t)| ≤ U := by
    have h := (pb (r (t+1)-(r t-gramOp (sampledMatrix 1) (r t)))).trans
      ((D.2.2.1 t).trans (mul_le_mul_of_nonneg_left (rb _) epos))
    simp only [map_sub] at h
    change |P (r (t+1))-(P (r t)-P (gramOp (sampledMatrix 1) (r t)))| ≤ U at h
    have eq := gramOp_eigenrow (N:=N) 1 b (by norm_num) (by norm_num) (r t)
    change P (gramOp (sampledMatrix 1) (r t)) = gamma N*P (r t) at eq
    rw [eq] at h
    convert h using 2; dsimp [a];ring
  have pdrift (t : ℕ) : |P (r t)-a^t*P (r 0)| ≤ U*t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show P (r (t+1))-a^(t+1)*P (r 0) =
        (P (r (t+1))-a*P (r t))+a*(P (r t)-a^t*P (r 0)) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg apos]
      exact (add_le_add (pnorm t) ((mul_le_of_le_one_left (abs_nonneg _) a1).trans ih)).trans_eq (by push_cast;ring)
  have μstep (t : ℕ) : |f (t+1)-f t + P (gramOp (sampledMatrix 1) (r t))| ≤ U := by
    have q := (D.2.2.2 t).trans (mul_le_mul_of_nonneg_left (rb t) epos)
    rw [population_row_factorization n (by omega) odd 1 (by norm_num) (by norm_num)] at q
    exact q
  have inv (t : ℕ) : |f t-P (r t)-(f 0-P (r 0))| ≤ 2*U*t := by
    induction t with
    | zero => simp
    | succ t ih =>
      let d := r (t+1)-(r t-gramOp (sampledMatrix 1) (r t))
      have hδ : |P d| ≤ U := (pb _).trans ((D.2.2.1 t).trans (mul_le_mul_of_nonneg_left (rb _) epos))
      have eq : f (t+1)-P (r (t+1))-(f 0-P (r 0)) =
          (f t-P (r t)-(f 0-P (r 0)))+
          (f (t+1)-f t+P (gramOp (sampledMatrix 1) (r t)))-P d := by simp only [d,map_sub]; ring
      rw [eq]
      exact ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ih (μstep t))) hδ)).trans_eq (by push_cast;ring)
  have train : trainedMean (CircleSeedIntegrability.path N (N^32) 1) T z = f T := by
    exact congrArg (CircleEscape.populationMean (1/sqrt ((N^32:ℕ):ℝ))) (iterate_eq_train N z T).symm
  have ref := actual_reference (N:=N) (by dsimp [N];omega) z (b*(1-a^T))
  have roweq : rowOp (fun _ : Fin N => b*(1-a^T)) (gridR N z) = (1-a^T)*P (r 0) := by
    change rowOp _ (gridR N z) = (1-a^T)*rowOp (fun _ : Fin N => b) (gridR N z)
    simp only [rowOp_apply,← Finset.mul_sum,mul_assoc]
    ring
  constructor
  · rw [train,←ref,roweq]
    change |f T - (f 0-(1-a^T)*P (r 0))| ≤ _
    rw [show f T - (f 0-(1-a^T)*P (r 0)) =
      (f T-P (r T)-(f 0-P (r 0)))+(P (r T)-a^T*P (r 0)) by ring]
    exact ((abs_add_le _ _).trans (add_le_add (inv T) (pdrift T))).trans_eq (by dsimp [U,e,r,iterate];ring)
  · rw [train,←actual_reference (N:=N) (by dsimp [N];omega) z b]
    change |f T - (f 0-P (r 0))| ≤ _
    rw [show f T - (f 0-P (r 0)) = P (r T)+(f T-P (r T)-(f 0-P (r 0))) by ring]
    exact ((abs_add_le _ _).trans (add_le_add (pb _) (inv T))).trans_eq (by dsimp [U,e,r,iterate];ring)

/-- True unit GD tracks the same-seed, exactly stopped reference. -/
theorem stopped_tracking (n : ℕ) (hN : 32 ≤ n+1) (odd : Odd (n+1)) (z : State ((n+1)^32))
    (G : GoodInit 1 (designRadius (n+1)) (designTolerance (n+1))
      (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (R0 : ‖gridR (n+1) z‖ ≤ ((n:ℝ)+1)^2) (T : ℕ) :
    let N := n+1
    let b := weight 1 n
    let a := 1-gamma N
    |trainedMean (CircleSeedIntegrability.path N (N^32) 1) T z -
      reference N (N^32) (b*(1-a^T)) z| ≤ 3*(66/(N:ℝ)^7)*‖gridR N z‖*T :=
  (endpoint_bounds n hN odd z G R0 T).1

/-- Population error at an arbitrary iteration, in terms of its observed grid RMS. -/
theorem terminal_tracking (n : ℕ) (hN : 32 ≤ n+1) (odd : Odd (n+1)) (z : State ((n+1)^32))
    (G : GoodInit 1 (designRadius (n+1)) (designTolerance (n+1))
      (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (R0 : ‖gridR (n+1) z‖ ≤ ((n:ℝ)+1)^2) (T : ℕ) :
    let N := n+1
    let b := weight 1 n
    |trainedMean (CircleSeedIntegrability.path N (N^32) 1) T z-reference N (N^32) b z| ≤
      ‖gridR N (iterate N z T)‖+2*(66/(N:ℝ)^7)*‖gridR N z‖*T :=
  (endpoint_bounds n hN odd z G R0 T).2

/-- Difference of the complete residual vectors, including every nonconstant
mode, at any update of the actual equal-rate learner. -/
theorem vector_tracking [NeZero N] (hN : 32≤N) (odd : Odd N) (z : State (N^32))
    (G : GoodInit 1 (designRadius N) (designTolerance N) (sampledMatrix 1) (fun _ : Fin N => k0 1) z)
    (init : ‖gridR N z‖≤(N:ℝ)^2) (T : ℕ) :
    ‖gridR N (iterate N z T)-((update N)^T) (gridR N z)‖≤(66/(N:ℝ)^7)*‖gridR N z‖*T := by
  let r := fun t => gridR N (iterate N z t)
  let f := fun t : ℕ => ((update N)^t) (gridR N z)
  have run := design_trajectory hN odd z G init
  have once := (norm_nonneg (update N)).trans (update_norm (by omega) odd)
  have bound : ‖update N‖≤1 := (update_norm (by omega) odd).trans (sub_le_self _ (by positivity))
  have cap (t : ℕ) : ‖r t‖≤‖gridR N z‖ := by
    have pos : 0≤designDecay N := by unfold designDecay; positivity
    have d := (design_bounds (by exact_mod_cast hN : (32:ℝ)≤N)).2.2.1
    have e : 0≤2*(30*designRadius N+3*designTolerance N) := by unfold designRadius designTolerance;positivity
    have d1 : designDecay N≤1 := by linarith only [d,e,once,norm_nonneg (update N)]
    exact (run.1 t).trans ((mul_le_mul_of_nonneg_right (pow_le_one₀ (sub_nonneg.mpr d1)
      (sub_le_self _ pos)) (norm_nonneg _)).trans_eq (one_mul _))
  change ‖r T-f T‖≤_
  induction T with
  | zero => simp [r,f,iterate]
  | succ t ih =>
    have eq : f (t+1)=update N (f t) := by dsimp only [f];rw [pow_succ'];rfl
    have h := norm_sub_le_norm_sub_add_norm_sub (r (t+1)) (update N (r t)) (f (t+1))
    have d := ((update N).le_opNorm (r t-f t)).trans
      ((mul_le_mul_of_nonneg_right bound (norm_nonneg _)).trans_eq (one_mul _))
    rw [eq,←map_sub] at h
    rw [eq]
    have a := (run.2.2.1 t).trans (mul_le_mul_of_nonneg_left (cap t) (by positivity : 0≤66/(N:ℝ)^7))
    exact (h.trans (add_le_add a (d.trans ih))).trans_eq (by push_cast;ring)

end CircleDiscreteTracking
