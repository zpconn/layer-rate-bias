module

public import CircleWeightedStep
import all CircleWeightedStep
import all CircleProjectedStep
import all CircleMeanDynamics
import all CircleActualTracking
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Tactic

/-! Exact finite-horizon mixed-tangent identity for the physical network.
Using integrals over [0,η] incorporates the step size, including at η=0. -/
@[expose] public section
noncomputable section
namespace CircleSegmentIdentity
open Real MeasureTheory Set CircleFlowPath CircleActualTracking CircleTangentDrift CircleWeightedStep
open CircleProjectedStep (signedMean)
variable {N m : ℕ}

private theorem integrate {f g : ℝ→ℝ} {η : ℝ} (ac : AbsolutelyContinuousOnInterval f 0 η)
    (df : ∀ᵐ s, s∈uIcc 0 η → HasDerivAt f (-(g s)) s) :
    f η-f 0= -(∫ s in (0:ℝ)..η, g s) := by
  rw [←ac.integral_deriv_eq_sub,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [df] with s h hs
  exact (h (uIoc_subset_uIcc hs)).deriv

def gridAction (τ η : ℝ) (N : ℕ) (z : State m) (x : ℝ×ℝ) :=
  ∫ s in (0:ℝ)..η, rowOp (mixedRow τ N z x s) (gridR N z)

def populationAction (τ η : ℝ) (N : ℕ) (z : State m) :=
  ∫ s in (0:ℝ)..η, rowOp (fun i => meanEntry τ (segment τ N z s) z (circleInput N i) (startGates z i)) (gridR N z)

theorem grid_step (τ η : ℝ) (N : ℕ) (z : State m) (x : ℝ×ℝ) :
    output (1/sqrt m) (segment τ N z η) x-output (1/sqrt m) z x= -gridAction τ η N z x := by
  have start : segment τ N z 0=z := by ext;simp [CircleWeightedStep.segment]
  simpa only [start,gridAction] using integrate (output_ac (segmentAC τ η N z) _ x) (observableAt τ η N z x)

theorem population_step (τ η : ℝ) (N : ℕ) (hm : 0<m) (z : State m) :
    CircleFlowMoments.mean (segment τ N z η)-CircleFlowMoments.mean z= -populationAction τ η N z := by
  let W := segment τ N z
  let M (s : ℝ) := CircleFlowMoments.mean (W s)
  have ac : AbsolutelyContinuousOnInterval M 0 η := by
    dsimp only [M]
    simp_rw [CircleMeanDynamics.mean_as_sum]
    exact (acsum Finset.univ _ (fun (j : Fin m) _ => (segmentAC τ η N z (j,0)).fun_mul
      (CircleMeanDynamics.feature_ac (segmentAC τ η N z) j))).const_mul _
  have reg : ∀ᵐ s, ∀ j, s∈uIcc 0 η →
      DifferentiableAt ℝ (fun t => CircleMeanDynamics.meanFeature (W t) j) s :=
    ae_all_iff.mpr fun j => (CircleMeanDynamics.feature_ac (segmentAC τ η N z) j).ae_differentiableAt
  have df : ∀ᵐ s, s∈uIcc 0 η → HasDerivAt M (-(rowOp (mixedMean τ N z s) (gridR N z))) s := by
    filter_upwards [reg] with s h hs
    have hp (p : Coord m) := segment_deriv τ N z p s
    have dh := (HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      (hp (j,0)).mul (CircleMeanDynamics.feature_deriv hp j (h j hs)))).const_mul (1/sqrt m)
    dsimp only [M];simp_rw [CircleMeanDynamics.mean_as_sum]
    apply dh.congr_deriv
    rw [←mean_contraction τ hm,CircleMeanDynamics.integrated_row]
  have start : W 0=z := by ext;simp [W,CircleWeightedStep.segment]
  have row (s : ℝ) : mixedMean τ N z s=(fun i => meanEntry τ (segment τ N z s) z (circleInput N i) (startGates z i)) := by funext i;rfl
  simpa only [M,start,populationAction,row,W] using integrate ac df

/-- The stepwise g−pH discrepancy, including its normalized action on
the *actual* residual at the start of the step. -/
def discrepancy (τ η : ℝ) (N : ℕ) (b : ℝ) (z : State m) :=
  populationAction τ η N z - (b/N)*∑ i : Fin N, gridAction τ η N z (circleInput N i)

theorem signed_step (τ η : ℝ) (N : ℕ) (hm : 0<m) (b : ℝ) (z : State m) :
    signedMean N b (segment τ N z η)-signedMean N b z= -discrepancy τ η N b z := by
  let w := segment τ N z η
  let residual₀ (z : State m) (i : Fin N) := output (1/sqrt m) z (circleInput N i)-circleLabel N i
  have obs (u : State m) : signedMean N b u=CircleFlowMoments.mean u-(b/N)*∑ i, residual₀ u i := by
    unfold signedMean gridR
    rw [rowOp_rms,←Finset.mul_sum]
    change _-b*(∑ i,residual₀ u i)/N=_
    ring
  have row : (∑ i,residual₀ w i)-(∑ i,residual₀ z i)= -∑ i,gridAction τ η N z (circleInput N i) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [residual₀,sub_sub_sub_cancel_right] using grid_step τ η N z (circleInput N i)
  rw [obs,obs]
  dsimp only [discrepancy]
  change CircleFlowMoments.mean w-_-(CircleFlowMoments.mean z-_) = _
  linarith only [population_step τ η N hm z,congrArg (fun y : ℝ => b/N*y) row]

/-- Equation (2) for the full nonlinear GD iterates. This equality holds
for every seed before any Gaussian estimates or width conditions are used. -/
theorem telescope (τ η : ℝ) (hn : 3≤N) (hm : 0<m) (z : State m) (b : ℝ) (T : ℕ) :
    let w := iterate τ η N z
    CircleFlowMoments.mean (w T)-CircleEscapeBridge.reference N m b z =
      rowOp (fun _ : Fin N => b) (gridR N (w T)) - ∑ t∈Finset.range T, discrepancy τ η N b (w t) := by
  intro w
  have sum (t : ℕ) : signedMean N b (w t)-signedMean N b z= -∑ s∈Finset.range t, discrepancy τ η N b (w s) := by
    induction t with
    | zero => simp [w,iterate]
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have upd := signed_step τ η N hm b (w t)
      change signedMean N b (w (t+1))-signedMean N b (w t)=_ at upd
      linarith only [ih,upd]
  rw [←actual_reference hn z b]
  have eq := sum T
  unfold signedMean at eq
  linarith only [eq]

end CircleSegmentIdentity
