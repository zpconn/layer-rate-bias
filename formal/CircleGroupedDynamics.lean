module

public import CircleGroupedBudget
public import CircleFiniteDynamics
public import CircleReadoutMargin
import all CircleSharpGD
import all CircleFiniteDynamics
import all CircleReadoutMargin
import all CircleRateTrajectory
import all CircleWidthTracking
import all CircleMeanDynamics
import all CircleSignedRow
import all CircleSignedAngular
import all CircleProjectedStep
import all CircleKernelGD
import all CircleReciprocalSpectral
import all CircleTangentDrift
import all CircleDiscreteTracking
import Mathlib.Tactic

/-! Sharp signed-row confinement with the true fixed-step residual path area. -/
@[expose] public section
noncomputable section
namespace CircleGroupedDynamics
open Real MeasureTheory Filter Topology Set Finset CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleDiscreteTracking CircleGridSpectrum CircleWidthTracking CircleRateTrajectory CircleProjectedStep CircleEscapeBridge
  CircleReciprocalSpectral CircleSharpGD CircleKernelGD
variable {N m : ℕ}

def drift (N : ℕ) (b : ℝ) := 22*CircleSignedAngular.G N b+4*CircleSignedAngular.B N b+2*(1+b)

structure Bounds (N : ℕ) [NeZero N] (b ρ R g v : ℝ) (z : State m) : Prop where
  residual : ‖gridR N z‖≤R
  energy : meanEnergy z≤4
  margin : CircleReadoutMargin.Good N ρ z
  gram : ∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤g
  signed : ∀ i : Fin N, |CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N i)|≤v

/-- Every prefix pays for the tentative next parameter segment. The same event
controls the signed trained observable and gives a convergent interpolating parameter vector. -/
theorem trajectory [NeZero N] (hn : 3≤N) (odd : Odd N) (hm : 0<m) (z : Seed m)
    {η b ρ R g v U : ℝ} (he : 0<η) (hu : η≤1) (hb : 0≤b) (p : 0≤ρ) (sr : ρ≤1)
    (hg : 0≤g) (hv : 0≤v) (_hU : 0≤U) (H : Bounds N b ρ R g v z)
    (area : ∀ t, η*(∑ j ∈ range t, ‖((propagator N η)^j) (gridR N z)‖)≤U)
    (cash : (2/sqrt m)*(2*U)≤ρ) (small : 2*(36*ρ+g)≤1/(π*(N:ℝ))^2) :
    (∀ t, rms η N z t≤(1-η*(1/(π*(N:ℝ))^2/2))^t*R ∧ budget η N z t≤2*U ∧
      |learnerMean η N z t-reference N m b z|≤b*rms η N z t+(v+drift N b*ρ)*(2*U)) ∧
    ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  let w := iterateAt N η z
  let r (t : ℕ) := gridR N (w t)
  let W := propagator N η
  let f (t : ℕ) := (W^t) (gridR N z)
  let A (t : ℕ) := η*‖r t‖
  let F (t : ℕ) := η*‖f t‖
  let D (t : ℕ) := η*‖r t-f t‖
  let e := 36*ρ+g
  let gap := 1/(π*(N:ℝ))^2
  let d := 2/sqrt (m:ℝ)
  let q := 1-η*(gap/2)
  let c := v+drift N b*ρ
  have np := NeZero.pos N
  have ep : 0≤e := by dsimp [e];positivity
  have gp : 0<gap := by dsimp [gap];positivity
  have gu : gap≤1 := CircleKernelGD.gap_le_one hn
  have eu : η*gap≤1 := (mul_le_mul_of_nonneg_left gu he.le).trans (by simpa using hu)
  have qp : 0≤q := by dsimp [q];linarith only [eu,mul_pos he gp]
  have dp : 0≤d := by dsimp [d];positivity
  have cv : 0≤c := by
    have gb : 0≤CircleSignedAngular.G N b := sqrt_nonneg _
    have bb : 0≤CircleSignedAngular.B N b := (abs_nonneg _).trans (le_max_left _ _)
    unfold c drift;positivity
  have pa (t : ℕ) : 0≤A t := mul_nonneg he.le (norm_nonneg _)
  have pd (t : ℕ) : 0≤D t := mul_nonneg he.le (norm_nonneg _)
  have tri (t : ℕ) : A t≤F t+D t := by
    have tr := norm_sub_le_norm_sub_add_norm_sub (r t) (f t) 0
    simpa only [A,F,D,sub_zero,add_comm,mul_add] using mul_le_mul_of_nonneg_left tr he.le
  have ar (t : ℕ) : total F t≤U := by simpa only [total,F,f,W,Finset.mul_sum] using area t
  let account (t : ℕ) := (∀ j, length (w t-z) j≤d*total A t*length z j) ∧
    D t+(η*gap)*total D t≤(η*e)*total A t ∧ ‖r t‖≤q^t*R ∧
    |signedMean N b (w t)-signedMean N b z|≤c*total A t
  have pay (t : ℕ) (h : account t) : total A (t+1)≤2*U :=
    paid_next (mul_pos he gp) eu (mul_nonneg he.le ep)
      (by dsimp [e,gap];nlinarith only [mul_le_mul_of_nonneg_left small he.le]) pd pa tri h.2.1 (ar (t+1))
  have tube (t : ℕ) (h : account t) : Tube ρ z (w t) := by
    have cost := (total_mono pa (Nat.le_succ t)).trans (pay t h)
    exact fun j => (h.1 j).trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left cost dp).trans cash) (sqrt_nonneg _))
  have acc (t : ℕ) : account t := by
    induction t with
    | zero =>
      refine ⟨fun j => ?_,?_,?_,?_⟩
      · simp [w,iterateAt,length,total]
      · simp [D,r,f,w,iterateAt,total]
      · simpa [r,w,iterateAt] using H.residual
      · simp [w,iterateAt,total]
    | succ t ih =>
      have money := (mul_le_mul_of_nonneg_left (pay t ih) dp).trans cash
      have move (s : ℝ) (hs : s∈Icc (0:ℝ) η) (j : Fin m) :
          length (seg N (w t) s-z) j≤d*total A (t+1)*length z j := by
        have mv := CircleFiniteDynamics.move hs.1 (tube t ih) sr (CircleNeuronSpeed.direction_le np (w t)) j
        have hmul := mul_le_mul_of_nonneg_right hs.2
          (show 0≤2/sqrt (m:ℝ)*‖r t‖*length z j by unfold length;positivity)
        exact mv.trans ((add_le_add (ih.1 j) hmul).trans_eq (by rw [total_succ];dsimp [d,A,r];ring))
      have along (s : ℝ) (hs : s∈Icc (0:ℝ) η) : Tube ρ z (seg N (w t) s) :=
        fun j => (move s hs j).trans (mul_le_mul_of_nonneg_right money (sqrt_nonneg _))
      have ge : ‖r (t+1)-W (r t)‖≤η*e*‖r t‖ := by
        apply grid_defect he.le np _ ep
        intro i s hs j
        have raw := CircleReadoutMargin.grid_segment_drift hm p sr s (tube t ih) (along s hs) H.energy H.margin.1 i j
        exact (abs_sub_le _ _ _).trans ((add_le_add raw (H.gram i j)).trans (by dsimp [e];linarith only [p]))
      have fstep : f (t+1)=W (f t) := by dsimp only [f];rw [pow_succ'];rfl
      have vel := norm_sub_le_norm_sub_add_norm_sub (r (t+1)) (W (r t)) (f (t+1))
      rw [fstep,←map_sub] at vel
      have defec : D (t+1)≤(1-η*gap)*D t+η*e*A t := by
        dsimp only [D,A]; rw [fstep]
        have cont := (add_le_add ge (CircleRateTrajectory.contractionAt hn odd he.le hu (r t-f t)))
        exact (mul_le_mul_of_nonneg_left (vel.trans cont) he.le).trans_eq (by dsimp [gap];ring)
      have inc := signed_increment he.le np hm b (w t) cv (fun s hs i => by
        have hd := CircleSignedRow.mixed_drift N hn odd hb p sr (along s hs) (tube t ih)
          H.energy H.margin.2 H.margin.1 i
        have eqrow : signedRow N b (w t) s i=CircleSignedRow.mixedRow N b (seg N (w t) s) (w t) (CircleEscape.gridPoint N i) :=
          (CircleSignedRow.mixedRow_eq N b hm _ _ _).symm
        rw [eqrow]
        have tr := abs_sub_le (CircleSignedRow.mixedRow N b (seg N (w t) s) (w t) (CircleEscape.gridPoint N i))
          (CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N i)) 0
        simp only [sub_zero] at tr
        exact tr.trans ((add_le_add hd (H.signed i)).trans_eq (by dsimp [c,drift];ring)))
      refine ⟨move η ⟨he.le,le_rfl⟩,?_,?_,?_⟩
      · rw [total_succ,total_succ];linarith only [defec,ih.2.1]
      · have tri' := norm_sub_le_norm_sub_add_norm_sub (r (t+1)) (W (r t)) 0
        simp only [sub_zero] at tri'
        have con := (add_le_add ge (CircleRateTrajectory.contractionAt hn odd he.le hu (r t)))
        have fac : η*e+(1-η*gap)≤q := by dsimp [q,e,gap];nlinarith only [mul_le_mul_of_nonneg_left small he.le]
        exact (tri'.trans con).trans (((by ring : η*e*‖r t‖+(1-η*gap)*‖r t‖=(η*e+(1-η*gap))*‖r t‖) ▸
          (mul_le_mul_of_nonneg_right fac (norm_nonneg _))).trans ((mul_le_mul_of_nonneg_left ih.2.2.1 qp).trans_eq (by ring)))
      · exact (abs_sub_le _ (signedMean N b (w t)) _).trans ((add_le_add inc ih.2.2.2).trans_eq
          (by rw [total_succ];dsimp [A,r];ring))
  constructor
  · intro t
    have bound := (total_mono pa (Nat.le_succ t)).trans (pay t (acc t))
    have area' : budget η N z t=total A t := by simp only [budget,total,A,r,w,rms,Finset.mul_sum]
    refine ⟨(acc t).2.2.1,area' ▸ bound,?_⟩
    let P := rowOp (fun _ : Fin N => b)
    have proj := (P.le_opNorm (r t)).trans (mul_le_mul_of_nonneg_right
      (rowOp_norm np hb (fun _ => (abs_of_nonneg hb).le)) (norm_nonneg _))
    rw [←actual_reference hn z b]
    change |CircleFlowMoments.mean (w t)-signedMean N b z|≤_
    rw [show CircleFlowMoments.mean (w t)-signedMean N b z=P (r t)+(signedMean N b (w t)-signedMean N b z) by unfold signedMean;dsimp only [P,r];ring]
    exact (abs_add_le ..).trans (add_le_add proj ((acc t).2.2.2.trans (mul_le_mul_of_nonneg_left bound cv)))
  · exact CircleFiniteDynamics.parameters_converge np z he (half_pos gp) qp sr (fun t => (acc t).2.2.1) (fun t => tube t (acc t))
end CircleGroupedDynamics
