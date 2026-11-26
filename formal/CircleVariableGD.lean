module

public import CircleWidthTracking
import all CircleWidthTracking
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleFlowPath
import all CircleTangentDrift
import all CircleMeanDynamics
import Mathlib.Tactic

/-! Mixed grid and population errors over a simultaneous step of any
nonnegative size. Confinement is required only along the segment traversed. -/
public section
noncomputable section
namespace CircleVariableGD
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking CircleDiscreteTracking
variable {N m : ℕ}
private theorem segmentAC (η : ℝ) (N : ℕ) (z : State m) (p : Coord m) :
    AbsolutelyContinuousOnInterval (fun s => seg N z s p) 0 η :=
  (show ContDiff ℝ 1 (fun s => z p+s*direction N z p) by fun_prop).contDiffOn.absolutelyContinuousOnInterval

private theorem observableAt (η : ℝ) (N : ℕ) (z : State m) (x : ℝ × ℝ) :
    ∀ᵐ s : ℝ, s ∈ uIcc 0 η → HasDerivAt (fun t => output (1/sqrt m) (seg N z t) x)
      (-(rowOp (mixedRow N z x s) (gridR N z))) s := by
  have hk : ∀ᵐ s, ∀ j : Fin m, s ∈ uIcc 0 η →
      DifferentiableAt ℝ (fun t => max (pre (seg N z t) j x) 0) s :=
    ae_all_iff.mpr fun j => (CircleFlowPath.acfeature (segmentAC η N z) j x).ae_differentiableAt
  filter_upwards [hk] with s hs H
  have h := output_deriv (c:=1/sqrt m) (fun p => seg_deriv N z p s) (fun j => hs j H)
    (fun j => actualGate (pre (seg N z s) j x)) (fun _ => actualGate_admissible _)
  rw [mixed_contraction] at h
  exact h

private theorem gridClose {η : ℝ} {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) η, Tube ρ z₀ (seg N z s)) (i : Fin N) :
    ∀ s ∈ Icc (0:ℝ) η, ∀ j, |mixedRow N z (circleInput N i) s j - K i j| ≤ 2*(30*ρ+3*u) := by
  intro s hs j
  apply two_rate_budget hρ hr G.energy (G.gridMargin i) (G.gridMargin j) _ (G.gram i j)
  exact entry_drift hm (by norm_num) (by norm_num) hρ (grid_unit i) (grid_unit j) (along s hs) tz
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)

private theorem predictionIncrement {η : ℝ} (hη : 0≤η) {x : ℝ × ℝ} (hn : 0<N) (z : State m) (k : Fin N → ℝ) {e : ℝ} (he : 0 ≤ e)
    (close : ∀ s ∈ Icc (0:ℝ) η, ∀ i, |mixedRow N z x s i - k i| ≤ e) :
    |output (1/sqrt m) (seg N z η) x-output (1/sqrt m) z x+η*rowOp k (gridR N z)| ≤ η*e*‖gridR N z‖ := by
  let b := rowOp k (gridR N z)
  let y := fun s => output (1/sqrt m) (seg N z s) x + s*b
  have ac : AbsolutelyContinuousOnInterval y 0 η :=
    (output_ac (segmentAC η N z) _ x).fun_add
      ((show ContDiff ℝ 1 (fun s : ℝ => s*b) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 η → |deriv y s| ≤ e * ‖gridR N z‖ := by
    filter_upwards [observableAt η N z x] with s hs H
    have hs' := hs (mem_uIcc_of_le H.1.le H.2)
    have h := hs'.add ((hasDerivAt_id s).mul_const b)
    change HasDerivAt y _ s at h
    rw [h.deriv,one_mul,neg_add_eq_sub]
    have norm := (rowOp_norm hn he (fun i => by simpa [abs_sub_comm] using close s ⟨H.1.le,H.2⟩ i))
    have hl := ((rowOp (k-mixedRow N z x s)).le_opNorm (gridR N z)).trans
      (mul_le_mul_of_nonneg_right norm (norm_nonneg _))
    simpa only [b,Real.norm_eq_abs,rowOp_sub,sub_apply] using hl
  have h := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    hη ac intervalIntegrable_const bound
  have z0 : seg N z 0 = z := by ext; simp [seg]
  simpa [y,z0,b,add_sub_right_comm,mul_left_comm,mul_assoc] using h


theorem grid_increment {η : ℝ} (hη : 0≤η) {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) η, Tube ρ z₀ (seg N z s)) :
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
    predictionIncrement hη hn z (K i) (by positivity) (gridClose hm G hρ hr tz along i)
  refine (Finset.sum_le_sum (g:=fun _ => (η*(2*(30*ρ+3*u))*‖r‖)^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  · simp [mul_comm,r]

theorem mean_increment {η : ℝ} (hη : 0≤η) {ρ u : ℝ} {z₀ z : State m}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (hn : 0 < N) (hm : 0 < m) (G : GoodInit 1 ρ u K kQ z₀) (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u)
    (tz : Tube ρ z₀ z) (along : ∀ s ∈ Icc (0:ℝ) η, Tube ρ z₀ (seg N z s)) :
    |CircleFlowMoments.mean (seg N z η)-CircleFlowMoments.mean z+η*rowOp kQ (gridR N z)| ≤
      η*(2*(30*ρ+3*u))*‖gridR N z‖ := by
  let W := seg N z
  let b := rowOp kQ (gridR N z)
  let y (s : ℝ) := CircleFlowMoments.mean (W s)+s*b
  have mac : AbsolutelyContinuousOnInterval (fun s => CircleFlowMoments.mean (W s)) 0 η := by
    simp_rw [CircleMeanDynamics.mean_as_sum]
    exact (acsum Finset.univ _ (fun (j : Fin m) _ => (segmentAC η N z (j,0)).fun_mul
      (CircleMeanDynamics.feature_ac (segmentAC η N z) j))).const_mul _
  have ac : AbsolutelyContinuousOnInterval y 0 η := mac.fun_add
    ((show ContDiff ℝ 1 (fun s : ℝ => s*b) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)
  have hreg : ∀ᵐ s, ∀ j, s ∈ uIcc 0 η →
      DifferentiableAt ℝ (fun t => CircleMeanDynamics.meanFeature (W t) j) s :=
    ae_all_iff.mpr fun j => (CircleMeanDynamics.feature_ac (segmentAC η N z) j).ae_differentiableAt
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 η → |deriv y s| ≤ 2*(30*ρ+3*u)*‖gridR N z‖ := by
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
    hη ac intervalIntegrable_const bound
  have z0 : W 0 = z := by ext; simp [W,seg]
  simpa [y,z0,W,b,add_sub_right_comm,show seg N z 0=z from z0,mul_left_comm,mul_assoc] using h


/-- Relative motion is linear in the actual step length, including for
steps larger than one. -/
theorem move_bound {z₀ z : State m} {ρ s : ℝ} (hn : 0<N) (tz : Tube ρ z₀ z)
    (hr : ρ≤1) (hs : 0≤s) (j : Fin m) :
    length (seg N z s-z₀) j ≤ length (z-z₀) j + s*((8/sqrt m)*‖gridR N z‖*length z₀ j) := by
  have cur := current_length tz j
  let d := 2/sqrt (m:ℝ)*‖gridR N z‖*length z j
  have dp : 0≤d := by dsimp [d,length];positivity
  have le (k : Fin 3) : |direction N z (j,k)| ≤ d :=
    coordinate_speed z _ _ hn (by norm_num : |(1:ℝ)|≤2) (startGates_admissible z) j k
  have sz : length (direction N z) j ≤ 2*d := by
    apply (sqrt_le_iff).2 ⟨by positivity,?_⟩
    apply (Finset.sum_le_sum (g:=fun _ => d^2) (fun k _ => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (le k) 2)).trans
    simp; nlinarith only [sq_nonneg d]
  have dl : length (seg N z s-z) j = s * length (direction N z) j := by
    simp only [CircleActualTracking.length_entity]
    have eq : (WithLp.toLp 2 (fun k : Fin 3 => (seg N z s-z) (j,k)) : EuclideanSpace ℝ (Fin 3)) =
      s • WithLp.toLp 2 (fun k : Fin 3 => direction N z (j,k)) := by ext k;change z (j,k)+s*direction N z (j,k)-z (j,k)=s*direction N z (j,k);ring
    rw [eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  have hcur := cur.trans (mul_le_mul_of_nonneg_right (by linarith : 1+ρ≤2) (sqrt_nonneg _))
  have scale : 2*d ≤ 8/sqrt m*‖gridR N z‖*length z₀ j := by
    have h := mul_le_mul_of_nonneg_left hcur (show 0≤(2/sqrt m)*‖gridR N z‖ by positivity)
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  have ht : length (seg N z s-z₀) j ≤ length (seg N z s-z) j + length (z-z₀) j := by
    simp only [CircleActualTracking.length_entity]
    exact norm_sub_le_norm_sub_add_norm_sub
      (WithLp.toLp 2 (fun k : Fin 3 => seg N z s (j,k)) : EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 (fun k : Fin 3 => z (j,k))) (WithLp.toLp 2 (fun k : Fin 3 => z₀ (j,k)))
  rw [dl] at ht
  exact ht.trans ((add_le_add (mul_le_mul_of_nonneg_left (sz.trans scale) hs) le_rfl).trans_eq (add_comm _ _))

end CircleVariableGD
