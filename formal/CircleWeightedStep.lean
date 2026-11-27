module

public import CircleProjectedStep
public import CircleNeuronSpeed
import all CircleProjectedStep
import all CircleActualTracking
import all CircleTangentDrift
import all CircleDiscreteTracking
import all CircleMeanDynamics
import all CircleFlowPath
import Mathlib.Tactic

/-! Simultaneous descent on both layers with an arbitrary hidden learning-rate
multiplier. The exact segment derivative uses the starting descent direction
and the current output Jacobian, including at trajectories that cross kinks. -/
@[expose] public section
noncomputable section
namespace CircleWeightedStep
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking
open CircleProjectedStep (signedMean)
variable {N m : ℕ}

def direction (τ : ℝ) (N : ℕ) (z : State m) : State m :=
  velocity τ (fun i => row (1/sqrt m) z (circleInput N i) (startGates z i))
    (CircleFlowPath.residual (circleInput N) (circleLabel N) (1/sqrt m) z)

def segment (τ : ℝ) (N : ℕ) (z : State m) (s : ℝ) : State m :=
  fun p => z p+s*direction τ N z p

def iterate (τ η : ℝ) (N : ℕ) (z : State m) : ℕ → State m
  | 0 => z
  | t+1 => segment τ N (iterate τ η N z t) η

theorem iterate_one (η : ℝ) (N : ℕ) (z : State m) (t : ℕ) :
    iterate 1 η N z t=CircleWidthTracking.iterateAt N η z t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterate,CircleWidthTracking.iterateAt,ih];rfl

/-- The Euclidean speed in the three physical coordinates of a single
neuron scales with the norm of the layer-rate diagonal. -/
theorem direction_le (τ : ℝ) (hτ : 0≤τ) (hn : 0<N) (z : State m) (j : Fin m) :
    length (direction τ N z) j≤max 1 τ*(‖gridR N z‖/sqrt m)*length z j := by
  let c := max 1 τ
  have cp : 0≤c := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have reg (p : Coord m) : |rate τ p|≤c := by
    unfold rate
    split
    · rw [abs_one];exact le_max_left _ _
    · rw [abs_of_nonneg hτ];exact le_max_right _ _
  have d (p : Coord m) : direction τ N z p=rate τ p*CircleDiscreteTracking.direction N z p := by
    simp only [direction,CircleDiscreteTracking.direction,velocity,rate,ite_self]
    ring
  have block : length (direction τ N z) j≤c*length (CircleDiscreteTracking.direction N z) j := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (mul_nonneg cp (sqrt_nonneg _))).mp
    change length (direction τ N z) j^2≤(c*length (CircleDiscreteTracking.direction N z) j)^2
    rw [mul_pow]
    unfold length
    simp only [sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _)),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [d,mul_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) (reg (j,k)) 2
    rw [sq_abs] at h
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  exact block.trans ((mul_le_mul_of_nonneg_left (CircleNeuronSpeed.direction_le hn z j) cp).trans_eq (by ring))
private theorem segmentAC (τ : ℝ) (η : ℝ) (N : ℕ) (z : State m) (p : Coord m) :
    AbsolutelyContinuousOnInterval (fun s => segment τ N z s p) 0 η :=
  (show ContDiff ℝ 1 (fun s => z p+s*direction τ N z p) by fun_prop).contDiffOn.absolutelyContinuousOnInterval

private theorem segment_deriv (τ : ℝ) (N : ℕ) (z : State m) (p : Coord m) (s : ℝ) :
    HasDerivAt (fun s => segment τ N z s p) (direction τ N z p) s := by
  simpa only [segment,id_eq,one_mul] using ((hasDerivAt_id s).mul_const (direction τ N z p)).const_add (z p)

private theorem mixed_contraction (τ : ℝ) (z v : State m) (x : ℝ × ℝ) (s : Fin m → ℝ) :
    pair (row (1/sqrt m) z x s) (direction τ N v) =
      -rowOp (fun i => entry τ z v x (circleInput N i) s (startGates v i)) (gridR N v) := by
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
def mixedRow (τ : ℝ) (N : ℕ) (z : State m) (x : ℝ × ℝ) (s : ℝ) (i : Fin N) :=
  entry τ (segment τ N z s) z x (circleInput N i)
    (fun j => actualGate (pre (segment τ N z s) j x)) (startGates z i)

theorem observableAt (τ : ℝ) (η : ℝ) (N : ℕ) (z : State m) (x : ℝ × ℝ) :
    ∀ᵐ s : ℝ, s ∈ uIcc 0 η → HasDerivAt (fun t => output (1/sqrt m) (segment τ N z t) x)
      (-(rowOp (mixedRow τ N z x s) (gridR N z))) s := by
  have hk : ∀ᵐ s, ∀ j : Fin m, s ∈ uIcc 0 η →
      DifferentiableAt ℝ (fun t => max (pre (segment τ N z t) j x) 0) s :=
    ae_all_iff.mpr fun j => (CircleFlowPath.acfeature (segmentAC τ η N z) j x).ae_differentiableAt
  filter_upwards [hk] with s hs H
  have h := output_deriv (c:=1/sqrt m) (fun p => segment_deriv τ N z p s) (fun j => hs j H)
    (fun j => actualGate (pre (segment τ N z s) j x)) (fun _ => actualGate_admissible _)
  rw [mixed_contraction] at h
  exact h

private theorem predictionIncrement (τ : ℝ) {η : ℝ} (hη : 0≤η) {x : ℝ × ℝ} (hn : 0<N) (z : State m) (k : Fin N → ℝ) {e : ℝ} (he : 0 ≤ e)
    (close : ∀ s ∈ Icc (0:ℝ) η, ∀ i, |mixedRow τ N z x s i - k i| ≤ e) :
    |output (1/sqrt m) (segment τ N z η) x-output (1/sqrt m) z x+η*rowOp k (gridR N z)| ≤ η*e*‖gridR N z‖ := by
  let b := rowOp k (gridR N z)
  let y := fun s => output (1/sqrt m) (segment τ N z s) x + s*b
  have ac : AbsolutelyContinuousOnInterval y 0 η :=
    (output_ac (segmentAC τ η N z) _ x).fun_add
      ((show ContDiff ℝ 1 (fun s : ℝ => s*b) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 η → |deriv y s| ≤ e * ‖gridR N z‖ := by
    filter_upwards [observableAt τ η N z x] with s hs H
    have hs' := hs (mem_uIcc_of_le H.1.le H.2)
    have h := hs'.add ((hasDerivAt_id s).mul_const b)
    change HasDerivAt y _ s at h
    rw [h.deriv,one_mul,neg_add_eq_sub]
    have norm := (rowOp_norm hn he (fun i => by simpa [abs_sub_comm] using close s ⟨H.1.le,H.2⟩ i))
    have hl := ((rowOp (k-mixedRow τ N z x s)).le_opNorm (gridR N z)).trans
      (mul_le_mul_of_nonneg_right norm (norm_nonneg _))
    simpa only [b,Real.norm_eq_abs,rowOp_sub,sub_apply] using hl
  have h := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    hη ac intervalIntegrable_const bound
  have z0 : segment τ N z 0 = z := by ext; simp [segment]
  simpa [y,z0,b,add_sub_right_comm,mul_left_comm,mul_assoc] using h


private def mixedMean (τ : ℝ) (N : ℕ) (z : State m) (s : ℝ) (i : Fin N) :=
  meanEntry τ (segment τ N z s) z (circleInput N i) (startGates z i)

private theorem mean_contraction (τ : ℝ) (hm : 0 < m) (z : State m) (s : ℝ) :
    (∫ v, pair (row (1/sqrt m) (segment τ N z s) (phase v) (fun j =>
        CircleMeanDynamics.gate (segment τ N z s) j v)) (direction τ N z) ∂angularLaw) =
      -rowOp (mixedMean τ N z s) (gridR N z) := by
  let a := CircleFlowPath.residual (circleInput N) (circleLabel N) (1/sqrt m) z
  simp_rw [mixed_contraction,gridR,rowOp_rms]
  rw [integral_neg,integral_div]
  have hi (i : Fin N) : Integrable (fun v => angleEntry τ (segment τ N z s) z
      (circleInput N i) (startGates z i) v*a i) angularLaw :=
    (angleEntry_integrable hm _ _ _ _ _).mul_const _
  change -((∫ v, ∑ i, angleEntry τ (segment τ N z s) z (circleInput N i) (startGates z i) v*a i ∂angularLaw)/N) = _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_const]
  rfl

theorem grid_defect (τ : ℝ) {η e : ℝ} {K : Matrix (Fin N) (Fin N) ℝ} (hη : 0≤η) (hn : 0<N)
    (z : State m) (he : 0≤e)
    (close : ∀ i : Fin N, ∀ s ∈ Icc (0:ℝ) η, ∀ j, |mixedRow τ N z (circleInput N i) s j-K i j|≤e) :
    ‖gridR N (segment τ N z η) - (gridR N z - η • gramOp K (gridR N z))‖ ≤ η*e*‖gridR N z‖ := by
  let r := gridR N z
  let a (i : Fin N) := output (1/sqrt m) (segment τ N z η) (circleInput N i) -
    output (1/sqrt m) z (circleInput N i) + η * rowOp (K i) r
  have eq : gridR N (segment τ N z η)-(r - η • gramOp K r) = rmsCoordinates a := by
    ext i
    change (output (1/sqrt m) (segment τ N z η) (circleInput N i)-circleLabel N i)/sqrt N -
      ((output (1/sqrt m) z (circleInput N i)-circleLabel N i)/sqrt N - η*(gramOp K r i)) = a i/sqrt N
    dsimp only [a]
    rw [gramOp_apply,rowOp_apply]
    generalize (output (1/sqrt m) (segment τ N z η) (circleInput N i)) = x
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
  have hb (i : Fin N) : |a i| ≤ η*e*‖r‖ :=
    predictionIncrement τ hη hn z (K i) (by positivity) (close i)
  refine (Finset.sum_le_sum (g:=fun _ => (η*e*‖r‖)^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  · simp [mul_comm,r]

def signedRow (τ : ℝ) (N : ℕ) (b : ℝ) (z : State m) (s : ℝ) (i : Fin N) :=
  meanEntry τ (segment τ N z s) z (circleInput N i) (startGates z i) -
  b*((∑ k : Fin N, mixedRow τ N z (circleInput N k) s i)/N)

/-- A pathwise row bound controls the change of the signed mean over the
whole step, retaining cancellation between the two projections. -/
theorem signed_increment (τ : ℝ) {η e : ℝ} (hη : 0≤η) (hn : 0<N) (hm : 0<m) (b : ℝ)
    (z : State m) (he : 0≤e) (close : ∀ s ∈ Icc (0:ℝ) η, ∀ i, |signedRow τ N b z s i|≤e) :
    |signedMean N b (segment τ N z η)-signedMean N b z| ≤ η*e*‖gridR N z‖ := by
  let W := segment τ N z
  let R (i : Fin N) (s : ℝ) := output (1/sqrt m) (W s) (circleInput N i)-circleLabel N i
  let M (s : ℝ) := CircleFlowMoments.mean (W s)
  let y (s : ℝ) := M s - (b/N)*∑ i, R i s
  have eq (s : ℝ) : signedMean N b (W s)=y s := by
    unfold signedMean gridR
    rw [rowOp_rms,←Finset.mul_sum]
    change _-b*(∑ i, R i s)/N=M s-(b/N)*(∑ i,R i s)
    dsimp only [M];ring
  have mac : AbsolutelyContinuousOnInterval M 0 η := by
    dsimp only [M]
    simp_rw [CircleMeanDynamics.mean_as_sum]
    exact (acsum Finset.univ _ (fun (j : Fin m) _ => (segmentAC τ η N z (j,0)).fun_mul
      (CircleMeanDynamics.feature_ac (segmentAC τ η N z) j))).const_mul _
  have ac : AbsolutelyContinuousOnInterval y 0 η :=
    mac.fun_sub ((acsum Finset.univ R (fun i _ => (output_ac (segmentAC τ η N z) _ _).fun_sub
      ((show ContDiff ℝ 1 (fun _ : ℝ => circleLabel N i) by fun_prop).contDiffOn.absolutelyContinuousOnInterval))).const_mul _)
  have hreg : ∀ᵐ s, ∀ j, s ∈ uIcc 0 η →
      DifferentiableAt ℝ (fun t => CircleMeanDynamics.meanFeature (W t) j) s :=
    ae_all_iff.mpr fun j => (CircleMeanDynamics.feature_ac (segmentAC τ η N z) j).ae_differentiableAt
  have hv := ae_all_iff.mpr (fun i : Fin N => observableAt τ η N z (circleInput N i))
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 η → |deriv y s|≤e*‖gridR N z‖ := by
    filter_upwards [hreg,hv] with s H V hs
    have hp (p : Coord m) := segment_deriv τ N z p s
    have us := mem_uIcc_of_le hs.1.le hs.2
    have dh := (HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      (hp (j,0)).mul (CircleMeanDynamics.feature_deriv hp j (H j us)))).const_mul (1/sqrt m)
    have dm : HasDerivAt M (-rowOp (mixedMean τ N z s) (gridR N z)) s := by
      dsimp only [M];simp_rw [CircleMeanDynamics.mean_as_sum]
      apply dh.congr_deriv
      rw [←mean_contraction τ hm,CircleMeanDynamics.integrated_row]
    have dr (i : Fin N) : HasDerivAt (R i) (-(rowOp (mixedRow τ N z (circleInput N i) s) (gridR N z))) s :=
      (V i us).sub_const _
    have dy := dm.sub ((HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => dr i)).const_mul (b/N))
    change HasDerivAt y _ s at dy
    rw [dy.deriv]
    have scalar : -rowOp (mixedMean τ N z s) (gridR N z) -
        b/N*∑ i, -rowOp (mixedRow τ N z (circleInput N i) s) (gridR N z) =
        -rowOp (signedRow τ N b z s) (gridR N z) := by
      let h := mixedMean τ N z s
      let D (i : Fin N) := mixedRow τ N z (circleInput N i) s
      let r := gridR N z
      change -rowOp h r - (b/N)*(∑ i, -rowOp (D i) r)= -rowOp (fun j => h j-b*((∑ i,D i j)/N)) r
      simp only [rowOp_apply,Finset.sum_neg_distrib,←Finset.sum_div,sub_mul,Finset.sum_sub_distrib]
      have linear : (∑ j,b*((∑ i,D i j)/N)*r j)=(b/N)*∑ i,∑ j,D i j*r j := by
        rw [Finset.sum_comm (s:=Finset.univ (α:=Fin N)) (t:=Finset.univ (α:=Fin N))
          (f:=fun i j => D i j*r j),Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [←Finset.sum_mul]
        ring
      rw [linear]; ring
    rw [scalar,abs_neg]
    exact ((rowOp (signedRow τ N b z s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (rowOp_norm hn he (close s ⟨hs.1.le,hs.2⟩)) (norm_nonneg _))
  have est := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    hη ac intervalIntegrable_const bound
  have z0 : W 0=z := by ext;simp [W,segment]
  rw [←eq,←eq,z0] at est
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_left_comm,mul_assoc] using est


end CircleWeightedStep
