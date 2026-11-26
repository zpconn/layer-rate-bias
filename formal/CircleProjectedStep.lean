module

public import CircleVariableGD
public import CircleRateTrajectory
public import CircleSignedRow
import all CircleVariableGD
import all CircleRateTrajectory
import all CircleDiscreteTracking
import all CircleFlowPath
import all CircleMeanDynamics
import all CircleActualTracking
import all CircleTangentDrift
import Mathlib.Tactic

/-! Integration of the actual mixed tangent tested against a signed
population-minus-grid observable, before taking absolute values. -/
public section
noncomputable section
namespace CircleProjectedStep
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking CircleDiscreteTracking
open CircleVariableGD
variable {N m : ℕ}

theorem grid_defect {η e : ℝ} {K : Matrix (Fin N) (Fin N) ℝ} (hη : 0≤η) (hn : 0<N)
    (z : State m) (he : 0≤e)
    (close : ∀ i : Fin N, ∀ s ∈ Icc (0:ℝ) η, ∀ j, |mixedRow N z (circleInput N i) s j-K i j|≤e) :
    ‖gridR N (seg N z η) - (gridR N z - η • gramOp K (gridR N z))‖ ≤ η*e*‖gridR N z‖ := by
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
  have hb (i : Fin N) : |a i| ≤ η*e*‖r‖ :=
    predictionIncrement hη hn z (K i) (by positivity) (close i)
  refine (Finset.sum_le_sum (g:=fun _ => (η*e*‖r‖)^2) (fun i _ => ?_)).trans_eq ?_
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  · simp [mul_comm,r]

def signedMean (N : ℕ) (b : ℝ) (z : State m) :=
  CircleFlowMoments.mean z-rowOp (fun _ : Fin N => b) (gridR N z)

def signedRow (N : ℕ) (b : ℝ) (z : State m) (s : ℝ) (i : Fin N) :=
  meanEntry 1 (seg N z s) z (circleInput N i) (startGates z i) -
  b*((∑ k : Fin N, mixedRow N z (circleInput N k) s i)/N)

/-- A pathwise row bound controls the change of the signed mean over the
whole step, retaining cancellation between the two projections. -/
theorem signed_increment {η e : ℝ} (hη : 0≤η) (hn : 0<N) (hm : 0<m) (b : ℝ)
    (z : State m) (he : 0≤e) (close : ∀ s ∈ Icc (0:ℝ) η, ∀ i, |signedRow N b z s i|≤e) :
    |signedMean N b (seg N z η)-signedMean N b z| ≤ η*e*‖gridR N z‖ := by
  let W := seg N z
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
    exact (acsum Finset.univ _ (fun (j : Fin m) _ => (segmentAC η N z (j,0)).fun_mul
      (CircleMeanDynamics.feature_ac (segmentAC η N z) j))).const_mul _
  have ac : AbsolutelyContinuousOnInterval y 0 η :=
    mac.fun_sub ((acsum Finset.univ R (fun i _ => (output_ac (segmentAC η N z) _ _).fun_sub
      ((show ContDiff ℝ 1 (fun _ : ℝ => circleLabel N i) by fun_prop).contDiffOn.absolutelyContinuousOnInterval))).const_mul _)
  have hreg : ∀ᵐ s, ∀ j, s ∈ uIcc 0 η →
      DifferentiableAt ℝ (fun t => CircleMeanDynamics.meanFeature (W t) j) s :=
    ae_all_iff.mpr fun j => (CircleMeanDynamics.feature_ac (segmentAC η N z) j).ae_differentiableAt
  have hv := ae_all_iff.mpr (fun i : Fin N => observableAt η N z (circleInput N i))
  have bound : ∀ᵐ s : ℝ, s ∈ Ioc 0 η → |deriv y s|≤e*‖gridR N z‖ := by
    filter_upwards [hreg,hv] with s H V hs
    have hp (p : Coord m) := seg_deriv N z p s
    have us := mem_uIcc_of_le hs.1.le hs.2
    have dh := (HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      (hp (j,0)).mul (CircleMeanDynamics.feature_deriv hp j (H j us)))).const_mul (1/sqrt m)
    have dm : HasDerivAt M (-rowOp (mixedMean N z s) (gridR N z)) s := by
      dsimp only [M];simp_rw [CircleMeanDynamics.mean_as_sum]
      apply dh.congr_deriv
      rw [←mean_contraction hm,CircleMeanDynamics.integrated_row]
    have dr (i : Fin N) : HasDerivAt (R i) (-(rowOp (mixedRow N z (circleInput N i) s) (gridR N z))) s :=
      (V i us).sub_const _
    have dy := dm.sub ((HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => dr i)).const_mul (b/N))
    change HasDerivAt y _ s at dy
    rw [dy.deriv]
    have scalar : -rowOp (mixedMean N z s) (gridR N z) -
        b/N*∑ i, -rowOp (mixedRow N z (circleInput N i) s) (gridR N z) =
        -rowOp (signedRow N b z s) (gridR N z) := by
      let h := mixedMean N z s
      let D (i : Fin N) := mixedRow N z (circleInput N i) s
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
    exact ((rowOp (signedRow N b z s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (rowOp_norm hn he (close s ⟨hs.1.le,hs.2⟩)) (norm_nonneg _))
  have est := CircleSharpTracking.endpoint_variation (C:=e) (q:=fun _ => ‖gridR N z‖)
    hη ac intervalIntegrable_const bound
  have z0 : W 0=z := by ext;simp [W,seg]
  rw [←eq,←eq,z0] at est
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_left_comm,mul_assoc] using est

end CircleProjectedStep
