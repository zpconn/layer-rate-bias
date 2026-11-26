module

public import CircleDiscreteTracking
public import CircleSharpGD
public import CircleNeuronSpeed
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleFlowPath
import all CircleFlowMoments
import all CircleMeanDynamics
import all CircleEscapeBridge
import all CircleInitializationCheck
import all CircleSeedIntegrability
import all CircleSharpGD
import Mathlib.Tactic

/-! Actual noncontractive finite-horizon tracking with a deterministic
step in [0,1]. The relative tube is closed from the number of steps,
independently of the small eigenvalues of the sampled tangent kernel. -/
@[expose] public section
noncomputable section
namespace CircleWidthTracking
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleDiscreteTracking CircleGridSpectrum CircleSpectrum CircleEscapeBridge
open scoped BigOperators
variable {N m : ℕ}

def iterateAt (N : ℕ) (η : ℝ) (z : State m) : ℕ → State m
  | 0 => z
  | t+1 => seg N (iterateAt N η z t) η

theorem segment_matches_step (N : ℕ) (z : State m) (η : ℝ) :
    CircleEscapeBridge.initial (seg N z η) = CircleEscape.step (CircleEscape.gridPoint N)
      (fun i => 1+(CircleEscape.gridPoint N i).re) (1/sqrt m) (η/(N*sqrt m)) (CircleEscapeBridge.initial z) := by
  let a := residual (circleInput N) (circleLabel N) (1/sqrt m) z
  have rr (i : Fin N) : CircleEscape.output (1/sqrt m) (CircleEscapeBridge.initial z) (CircleEscape.gridPoint N i) -
      (1+(CircleEscape.gridPoint N i).re) = a i := by rw [output_complex]; rfl
  have pp (i : Fin N) (j : Fin m) : inner ℝ ((CircleEscapeBridge.initial z).w j) (CircleEscape.gridPoint N i) =
      pre z j (circleInput N i) := pre_complex _ _ _
  simp only [CircleEscape.step,rr,CircleEscape.feature,CircleEscape.gate,pp]
  unfold CircleEscapeBridge.initial
  congr 1
  · ext j
    change z (j,0)+η*direction N z (j,0) = z (j,0) - _*_
    simp only [direction,velocity,gradient,rate,row, ↓reduceIte, Matrix.cons_val_zero]
    change z (j,0) + η*(-(1:ℝ)*((1/N)*∑ i, a i * ((1/sqrt m)*max (pre z j (circleInput N i)) 0))) = _
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul,Finset.mul_sum,← Finset.sum_neg_distrib,sub_eq_add_neg,neg_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros; ring
  · funext j
    apply Complex.ext
    all_goals
      simp only [Complex.sub_re,Complex.sub_im,Complex.real_smul,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_sum,Complex.im_sum,
        zero_mul,sub_zero,add_zero,seg,direction,velocity,gradient,rate,row,
        startGates,actualGate,Matrix.cons_val_one,Matrix.cons_val_zero,Fin.isValue]
    all_goals
      simp only [show (1:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 0 by decide, ↓reduceIte,
        neg_mul,one_mul,div_eq_mul_inv,mul_inv_rev]
      congr 1
      simp only [mul_neg,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [a,circleInput]
      ring

theorem iterateAt_eq_train (N : ℕ) (η : ℝ) (z : State m) (T : ℕ) :
    CircleEscapeBridge.initial (iterateAt N η z T) =
      CircleInitializationCheck.train N m η (CircleEscapeBridge.initial z) T := by
  induction T with
  | zero => rfl
  | succ t ih => rw [iterateAt,CircleInitializationCheck.train,segment_matches_step,ih]

private theorem fractional_increment {η : ℝ} (hη : 0≤η) (hc : η≤1) {x : ℝ × ℝ} (hn : 0<N) (z : State m) (k : Fin N → ℝ) {e : ℝ} (he : 0 ≤ e)
    (close : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, |mixedRow N z x s i - k i| ≤ e) :
    |output (1/sqrt m) (seg N z η) x-output (1/sqrt m) z x+η*rowOp k (gridR N z)| ≤ η*e*‖gridR N z‖ := by
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
  have sub : uIcc 0 η ⊆ uIcc (0:ℝ) 1 := by rw [uIcc_of_le hη,uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right hc
  have h := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    hη (ac.mono sub) intervalIntegrable_const (bound.mono fun _ h hs => h ⟨hs.1,hs.2.trans hc⟩)
  have z0 : seg N z 0 = z := by ext; simp [seg]
  simpa [y,z0,b,add_sub_right_comm,mul_left_comm,mul_assoc] using h


private theorem fractional_grid {η : ℝ} (hη : 0≤η) (hc : η≤1) {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) :
    ‖gridR N (seg N z η) - (gridR N z - η • gramOp K (gridR N z))‖ ≤ η*(2*(30*ρ+3*u))*‖gridR N z‖ := by
  let r := gridR N z
  let a (i : Fin N) := output (1/sqrt m) (seg N z η) (circleInput N i) -
    output (1/sqrt m) z (circleInput N i) + η * rowOp (K i) r
  have eq : gridR N (seg N z η)-(r - η • gramOp K r) = rmsCoordinates a := by
    ext i
    change (output (1/sqrt m) (seg N z η) (circleInput N i)-circleLabel N i)/sqrt N -
      ((output (1/sqrt m) z (circleInput N i)-circleLabel N i)/sqrt N - η*(gramOp K r i)) = a i/sqrt N
    dsimp only [a]
    rw [gramOp_apply,rowOp_apply]
    generalize (output (1/sqrt m) (seg N z η) (circleInput N i)) = x
    generalize (output (1/sqrt m) z (circleInput N i)) = y
    generalize circleLabel N i = h
    generalize (∑ j, K i j * r.ofLp j) = b
    have ns := sq_sqrt (Nat.cast_nonneg N)
    generalize sqrt (N:ℝ) = d at *
    have dpos : d≠0 := by intro h; rw [h] at ns; have hNreal : (0:ℝ)<N := Nat.cast_pos.mpr hn; nlinarith
    field_simp
    nlinarith only [congrArg (fun t : ℝ => η*b*t) ns]
  rw [eq, ←Real.sqrt_sq (norm_nonneg _),rmsCoordinates_norm_sq]
  apply (sqrt_le_iff).2 ⟨by positivity,?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  have hb (i : Fin N) : |a i| ≤ η*(2*(30*ρ+3*u))*‖r‖ :=
    fractional_increment hη hc hn z (K i) (by positivity) (grid_close hm G hρ hr tz along i)
  refine (Finset.sum_le_sum (g:=fun _ => (η*(2*(30*ρ+3*u))*‖r‖)^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  · simp [mul_comm,r]

private theorem fractional_mean {η : ℝ} (hη : 0≤η) (hc : η≤1) {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) :
    |CircleFlowMoments.mean (seg N z η)-CircleFlowMoments.mean z+η*rowOp kQ (gridR N z)| ≤
      η*(2*(30*ρ+3*u))*‖gridR N z‖ := by
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
  have sub : uIcc 0 η ⊆ uIcc (0:ℝ) 1 := by rw [uIcc_of_le hη,uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right hc
  have h := CircleSharpTracking.endpoint_variation (C:=2*(30*ρ+3*u)) (q:=fun _ => ‖gridR N z‖)
    hη (ac.mono sub) intervalIntegrable_const (bound.mono fun _ h hs => h ⟨hs.1,hs.2.trans hc⟩)
  have z0 : W 0 = z := by ext; simp [W,seg]
  simpa [y,z0,W,b,add_sub_right_comm,show seg N z 0=z from z0,mul_left_comm,mul_assoc] using h

open CircleKernelGD CircleFlowTracking

private theorem nonexpansive [NeZero N] (hn : 3≤N) (odd : Odd N) {η : ℝ} (hη : 0≤η) (hc : η≤1)
    (v : EuclideanSpace ℝ (Fin N)) : ‖v-η • gramOp (sampledMatrix 1) v‖≤‖v‖ := by
  have h := contraction hn odd v
  have h' : ‖v-gramOp (sampledMatrix 1) v‖≤‖v‖ :=
    h.trans ((mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) (norm_nonneg _)).trans_eq (one_mul _))
  rw [show v-η • gramOp (sampledMatrix 1) v =
    (1-η) • v + η • (v-gramOp (sampledMatrix 1) v) by module]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hη,abs_of_nonneg (sub_nonneg.mpr hc)]
  nlinarith only [mul_le_mul_of_nonneg_left h' hη]

/-- Relative motion of a whole neuron on one tentative update segment. -/
private theorem move_neuron {ρ s : ℝ} {z w : State m} (hn : 0<N) (hs : s∈Icc (0:ℝ) 1)
    (tube : Tube ρ z w) (j : Fin m) :
    length (seg N w s-z) j ≤ length (w-z) j+((1+ρ)/sqrt m)*‖gridR N w‖*length z j := by
  have eq : length (seg N w s-w) j = s*length (direction N w) j := by
    simp only [CircleActualTracking.length_entity]
    have vec : (WithLp.toLp 2 (fun k : Fin 3 => (seg N w s-w) (j,k)) : EuclideanSpace ℝ (Fin 3)) =
      s • WithLp.toLp 2 (fun k : Fin 3 => direction N w (j,k)) := by
      ext k;change w (j,k)+s*direction N w (j,k)-w (j,k)=s*direction N w (j,k);ring
    rw [vec,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
  have tri : length (seg N w s-z) j ≤ length (seg N w s-w) j+length (w-z) j := by
    simp only [CircleActualTracking.length_entity]
    exact norm_sub_le_norm_sub_add_norm_sub
      (WithLp.toLp 2 (fun k : Fin 3 => seg N w s (j,k)) : EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 (fun k : Fin 3 => w (j,k))) (WithLp.toLp 2 (fun k : Fin 3 => z (j,k)))
  have d := (CircleNeuronSpeed.direction_le hn w j).trans
    (mul_le_mul_of_nonneg_left (CircleActualTracking.current_length tube j) (by positivity))
  rw [eq] at tri
  have d' : length (direction N w) j≤(1+ρ)/sqrt m*‖gridR N w‖*length z j := d.trans_eq (by ring)
  have sm : s*length (direction N w) j≤length (direction N w) j := mul_le_of_le_one_left (sqrt_nonneg _) hs.2
  exact tri.trans (by linarith only [sm,d'])

/-- The whole step segment is controlled by a time budget alone. -/
private theorem finite_budget [NeZero N] (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    {η ρ u R : ℝ} {z₀ : State m} (hη : 0≤η) (hc : η≤1) (T : ℕ)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => k0 1) z₀)
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hR : ‖gridR N z₀‖≤R)
    (drift : T*((2*(1+ρ))/sqrt m*R)≤ρ) (err : T*(2*(30*ρ+3*u))≤1/2) :
    let z := iterateAt N η z₀
    let e := 2*(30*ρ+3*u)
    ∀ t<T, ‖gridR N (z (t+1))-(gridR N (z t)-η • gramOp (sampledMatrix 1) (gridR N (z t)))‖≤2*e*R ∧
      |CircleFlowMoments.mean (z (t+1))-CircleFlowMoments.mean (z t)+η*rowOp (fun _ : Fin N => k0 1)
        (gridR N (z t))|≤2*e*R := by
  intro z e
  have ep : 0≤e := by dsimp [e];positivity
  have Rp := (norm_nonneg _).trans hR
  let d := (2*(1+ρ))/sqrt m*R
  have dp : 0≤d := by dsimp [d];positivity
  have run (t : ℕ) (ht : t≤T) :
      ‖gridR N (z t)‖≤R+(2*e*R)*t ∧ ∀ j, length (z t-z₀) j ≤ (t*d)*length z₀ j := by
    induction t with
    | zero => simpa [z,iterateAt,length] using hR
    | succ t ih =>
      have H := ih (by omega)
      have et : t*e≤1/2 := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show t≤T by omega)) ep).trans err
      have cap : ‖gridR N (z t)‖≤2*R := H.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right et Rp])
      have tb (s : ℕ) (hs : s≤T) : (s:ℝ)*d≤ρ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) dp).trans drift
      have cur : Tube ρ z₀ (z t) := fun j => (H.2 j).trans (mul_le_mul_of_nonneg_right (tb t (by omega)) (sqrt_nonneg _))
      have step (s : ℝ) (hs : s∈Icc 0 1) (j : Fin m) :
          length (seg N (z t) s-z₀) j ≤ ((t+1:ℕ)*d)*length z₀ j := by
        have mov := move_neuron (N:=N) (by omega) hs cur j
        have scaled := mul_le_mul_of_nonneg_left cap (show 0≤(1+ρ)/sqrt (m:ℝ) by positivity)
        have dn : (1+ρ)/sqrt m*‖gridR N (z t)‖≤d := scaled.trans_eq (by dsimp only [d];ring)
        exact mov.trans ((add_le_add (H.2 j) (mul_le_mul_of_nonneg_right dn (show 0≤length z₀ j from sqrt_nonneg _))).trans_eq (by push_cast;ring))
      have along (s : ℝ) (hs : s∈Icc 0 1) : Tube ρ z₀ (seg N (z t) s) := fun j =>
        (step s hs j).trans (mul_le_mul_of_nonneg_right (tb _ ht) (sqrt_nonneg _))
      refine ⟨?_,step η ⟨hη,hc⟩⟩
      have hF := fractional_grid hη hc (by omega) hm G hρ hr hu cur along
      have hU := nonexpansive hn odd hη hc (gridR N (z t))
      have hk : η*e*‖gridR N (z t)‖≤2*e*R := by
        have h1 := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ep hc) (norm_nonneg (gridR N (z t)))
        nlinarith only [h1,mul_le_mul_of_nonneg_left cap ep]
      have h := norm_le_norm_sub_add (gridR N (z (t+1))) (gridR N (z t)-η • gramOp (sampledMatrix 1) (gridR N (z t)))
      exact h.trans ((add_le_add (hF.trans hk) (hU.trans H.1)).trans_eq (by push_cast;ring))
  intro t ht
  have H := run t (by omega)
  have et : t*e≤1/2 := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show t≤T by omega)) ep).trans err
  have cap : ‖gridR N (z t)‖≤2*R := H.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right et Rp])
  have tb (s : ℕ) (hs : s≤T) : (s:ℝ)*d≤ρ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) dp).trans drift
  have cur : Tube ρ z₀ (z t) := fun j => (H.2 j).trans (mul_le_mul_of_nonneg_right (tb t (by omega)) (sqrt_nonneg _))
  have along (s : ℝ) (hs : s∈Icc 0 1) : Tube ρ z₀ (seg N (z t) s) := by
    intro j
    have mov := move_neuron (N:=N) (by omega) hs cur j
    have scaled := mul_le_mul_of_nonneg_left cap (show 0≤(1+ρ)/sqrt (m:ℝ) by positivity)
    have dn : (1+ρ)/sqrt m*‖gridR N (z t)‖≤d := scaled.trans_eq (by dsimp only [d];ring)
    apply mov.trans ((add_le_add (H.2 j) (mul_le_mul_of_nonneg_right dn (show 0≤length z₀ j from sqrt_nonneg _))).trans ?_)
    rw [← add_mul,← add_one_mul]
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    simpa [add_comm] using tb (t+1) ht
  have hk : η*e*‖gridR N (z t)‖≤2*e*R := by
    have h1 := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left ep hc) (norm_nonneg (gridR N (z t)))
    nlinarith only [h1,mul_le_mul_of_nonneg_left cap ep]
  exact ⟨(fractional_grid hη hc (by omega) hm G hρ hr hu cur along).trans hk,
    (fractional_mean hη hc (by omega) hm G hρ hr hu cur along).trans hk⟩

def stoppedCoefficient (n T : ℕ) (η : ℝ) := weight 1 n*(1-(1-η*gamma (n+1))^T)

theorem stopped_tracking_neuron (n m T : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η ρ u R : ℝ} (z : State m) (hη : 0≤η) (hc : η≤1)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hR : ‖gridR (n+1) z‖≤R)
    (drift : T*((2*(1+ρ))/sqrt m*R)≤ρ) (err : T*(2*(30*ρ+3*u))≤1/2) :
    |trainedMean (CircleSeedIntegrability.path (n+1) m η) T z -
      reference (n+1) m (stoppedCoefficient n T η) z| ≤ 6*(2*(30*ρ+3*u))*R*T := by
  let N := n+1
  let b := weight 1 n
  let a := 1-η*gamma N
  let r := fun t => gridR N (iterateAt N η z t)
  let f := fun t => CircleFlowMoments.mean (iterateAt N η z t)
  let P := rowOp (fun _ : Fin N => b)
  let U := 2*(2*(30*ρ+3*u))*R
  have D := finite_budget hn odd hm hη hc T G hρ hr hu hR drift err
  have ng : 0≤gamma N := (show (0:ℝ)≤3/π^2 by positivity).trans gamma_bounds.1
  have apos : 0≤a := sub_nonneg.mpr ((mul_le_of_le_one_left ng hc).trans gamma_bounds.2)
  have a1 : a≤1 := sub_le_self _ (mul_nonneg hη ng)
  have pb (v : EuclideanSpace ℝ (Fin N)) : |P v| ≤ ‖v‖ :=
    (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_right
      (rowOp_norm (by dsimp [N];omega) zero_le_one (fun _ => weight_abs_le_one n 1 (by norm_num))) (norm_nonneg v)).trans_eq (one_mul _))
  have pnorm (t : ℕ) (ht : t<T) : |P (r (t+1)) - a*P (r t)| ≤ U := by
    have h := (pb (r (t+1)-(r t-η • gramOp (sampledMatrix 1) (r t)))).trans
      (D t ht).1
    simp only [map_sub,map_smul,smul_eq_mul] at h
    change |P (r (t+1))-(P (r t)-η*P (gramOp (sampledMatrix 1) (r t)))| ≤ U at h
    have eq := gramOp_eigenrow (N:=N) 1 b (by norm_num) (by norm_num) (r t)
    change P (gramOp (sampledMatrix 1) (r t)) = gamma N*P (r t) at eq
    rw [eq] at h
    convert h using 2; dsimp [a];ring
  have pdrift (t : ℕ) (ht : t≤T) : |P (r t)-a^t*P (r 0)| ≤ U*t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show P (r (t+1))-a^(t+1)*P (r 0) =
        (P (r (t+1))-a*P (r t))+a*(P (r t)-a^t*P (r 0)) by ring]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg apos]
      exact (add_le_add (pnorm t (by omega)) ((mul_le_of_le_one_left (abs_nonneg _) a1).trans (ih (by omega)))).trans_eq (by push_cast;ring)
  have μstep (t : ℕ) (ht : t<T) : |f (t+1)-f t + η*P (gramOp (sampledMatrix 1) (r t))| ≤ U := by
    have q := (D t ht).2
    rw [population_row_factorization n (by omega) odd 1 (by norm_num) (by norm_num)] at q
    exact q
  have inv (t : ℕ) (ht : t≤T) : |f t-P (r t)-(f 0-P (r 0))| ≤ 2*U*t := by
    induction t with
    | zero => simp
    | succ t ih =>
      let d := r (t+1)-(r t-η • gramOp (sampledMatrix 1) (r t))
      have hδ : |P d| ≤ U := (pb _).trans (D t ht).1
      have eq : f (t+1)-P (r (t+1))-(f 0-P (r 0)) =
          (f t-P (r t)-(f 0-P (r 0)))+
          (f (t+1)-f t+η*P (gramOp (sampledMatrix 1) (r t)))-P d := by simp only [d,map_sub,map_smul,smul_eq_mul]; ring
      rw [eq]
      exact ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (ih (by omega)) (μstep t (by omega)))) hδ)).trans_eq (by push_cast;ring)
  have train : trainedMean (CircleSeedIntegrability.path N m η) T z = f T := by
    exact congrArg (CircleEscape.populationMean (1/sqrt (m:ℝ))) (iterateAt_eq_train N η z T).symm
  have ref := actual_reference (N:=N) (by dsimp [N];omega) z (b*(1-a^T))
  have roweq : rowOp (fun _ : Fin N => b*(1-a^T)) (gridR N z) = (1-a^T)*P (r 0) := by
    change rowOp _ (gridR N z) = (1-a^T)*rowOp (fun _ : Fin N => b) (gridR N z)
    simp only [rowOp_apply,← Finset.mul_sum,mul_assoc]
    ring
  change |trainedMean (CircleSeedIntegrability.path N m η) T z-reference N m (b*(1-a^T)) z|≤_
  rw [train,←ref,roweq]
  change |f T - (f 0-(1-a^T)*P (r 0))| ≤ _
  rw [show f T - (f 0-(1-a^T)*P (r 0)) =
      (f T-P (r T)-(f 0-P (r 0)))+(P (r T)-a^T*P (r 0)) by ring]
  exact ((abs_add_le _ _).trans (add_le_add (inv T le_rfl) (pdrift T le_rfl))).trans_eq (by dsimp [U];ring)

theorem stopped_tracking (n m T : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η ρ u R : ℝ} (z : State m) (hη : 0≤η) (hc : η≤1)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hR : ‖gridR (n+1) z‖≤R)
    (drift : T*(16/sqrt m*R)≤ρ) (err : T*(2*(30*ρ+3*u))≤1/2) :
    |trainedMean (CircleSeedIntegrability.path (n+1) m η) T z -
      reference (n+1) m (stoppedCoefficient n T η) z| ≤ 6*(2*(30*ρ+3*u))*R*T := by
  apply stopped_tracking_neuron n m T hn odd hm z hη hc G hρ hr hu hR _ err
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by linarith : 2*(1+ρ)≤16) (sqrt_nonneg _)) ((norm_nonneg _).trans hR))
      (Nat.cast_nonneg T)).trans drift

end CircleWidthTracking
