module

public import CircleWidthTracking
import all CircleWidthTracking
public import CircleVariableGD
public import CircleReciprocal
public import CircleSharpGD
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


/-! True reciprocal-step trajectories on a finite horizon. -/
public section
noncomputable section
namespace CircleReciprocalTracking
open Real MeasureTheory Set CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleDiscreteTracking CircleGridSpectrum CircleSpectrum CircleEscapeBridge CircleWidthTracking
open CircleKernelGD CircleFlowTracking
open scoped BigOperators
variable {N m : ℕ}

/-- The whole step segment is controlled by a time budget alone. -/
theorem finite_budget [NeZero N] (hn : 3≤N) (hm : 0<m)
    {η ρ u R : ℝ} {z₀ : State m} (hη : 0≤η) (hc : η≤4) (T : ℕ)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => k0 1) z₀)
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hR : ‖gridR N z₀‖≤R)
    (linear : ∀ v : EuclideanSpace ℝ (Fin N), ‖v-η • gramOp (sampledMatrix 1) v‖≤‖v‖)
    (drift : T*(64/sqrt m*R)≤ρ) (err : T*(2*(30*ρ+3*u))≤1/8) :
    let z := iterateAt N η z₀
    let e := 2*(30*ρ+3*u)
    ∀ t<T, ‖gridR N (z (t+1))-(gridR N (z t)-η • gramOp (sampledMatrix 1) (gridR N (z t)))‖≤8*e*R ∧
      |CircleFlowMoments.mean (z (t+1))-CircleFlowMoments.mean (z t)+η*rowOp (fun _ : Fin N => k0 1)
        (gridR N (z t))|≤8*e*R := by
  intro z e
  have ep : 0≤e := by dsimp [e];positivity
  have Rp := (norm_nonneg _).trans hR
  let d := 64/sqrt m*R
  have dp : 0≤d := by dsimp [d];positivity
  have run (t : ℕ) (ht : t≤T) :
      ‖gridR N (z t)‖≤R+(8*e*R)*t ∧ ∀ j, length (z t-z₀) j ≤ (t*d)*length z₀ j := by
    induction t with
    | zero => simpa [z,iterateAt,length] using hR
    | succ t ih =>
      have H := ih (by omega)
      have et : t*e≤1/8 := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show t≤T by omega)) ep).trans err
      have cap : ‖gridR N (z t)‖≤2*R := H.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right et Rp])
      have tb (s : ℕ) (hs : s≤T) : (s:ℝ)*d≤ρ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) dp).trans drift
      have cur : Tube ρ z₀ (z t) := fun j => (H.2 j).trans (mul_le_mul_of_nonneg_right (tb t (by omega)) (sqrt_nonneg _))
      have step (s : ℝ) (hs : s∈Icc 0 η) (j : Fin m) :
          length (seg N (z t) s-z₀) j ≤ ((t+1:ℕ)*d)*length z₀ j := by
        have mov := CircleVariableGD.move_bound (N:=N) (by omega) cur hr hs.1 j
        have scaled := mul_le_mul (hs.2.trans hc) cap (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
        have dn : s*(8/sqrt m*‖gridR N (z t)‖*length z₀ j) ≤ d*length z₀ j := by
          have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left scaled (show (0:ℝ)≤8/sqrt m by positivity)) (show 0≤length z₀ j from sqrt_nonneg _)
          convert hh using 1 <;> (try dsimp only [d]) <;> ring
        exact mov.trans ((add_le_add (H.2 j) dn).trans_eq (by push_cast;ring))
      have along (s : ℝ) (hs : s∈Icc 0 η) : Tube ρ z₀ (seg N (z t) s) := fun j =>
        (step s hs j).trans (mul_le_mul_of_nonneg_right (tb _ ht) (sqrt_nonneg _))
      refine ⟨?_,step η ⟨hη,le_rfl⟩⟩
      have hF := CircleVariableGD.grid_increment hη (by omega) hm G hρ hr hu cur along
      have hU := linear (gridR N (z t))
      have hk : η*e*‖gridR N (z t)‖≤8*e*R := by
        have hh := mul_le_mul hc cap (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
        nlinarith only [mul_le_mul_of_nonneg_left hh ep]
      have h := norm_le_norm_sub_add (gridR N (z (t+1))) (gridR N (z t)-η • gramOp (sampledMatrix 1) (gridR N (z t)))
      exact h.trans ((add_le_add (hF.trans hk) (hU.trans H.1)).trans_eq (by push_cast;ring))
  intro t ht
  have H := run t (by omega)
  have et : t*e≤1/8 := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show t≤T by omega)) ep).trans err
  have cap : ‖gridR N (z t)‖≤2*R := H.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right et Rp])
  have tb (s : ℕ) (hs : s≤T) : (s:ℝ)*d≤ρ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hs) dp).trans drift
  have cur : Tube ρ z₀ (z t) := fun j => (H.2 j).trans (mul_le_mul_of_nonneg_right (tb t (by omega)) (sqrt_nonneg _))
  have along (s : ℝ) (hs : s∈Icc 0 η) : Tube ρ z₀ (seg N (z t) s) := by
    intro j
    have mov := CircleVariableGD.move_bound (N:=N) (by omega) cur hr hs.1 j
    have scaled := mul_le_mul (hs.2.trans hc) cap (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
    have dn : s*(8/sqrt m*‖gridR N (z t)‖*length z₀ j) ≤ d*length z₀ j := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left scaled (show (0:ℝ)≤8/sqrt m by positivity)) (show 0≤length z₀ j from sqrt_nonneg _)
      convert hh using 1 <;> (try dsimp only [d]) <;> ring
    apply mov.trans ((add_le_add (H.2 j) dn).trans ?_)
    rw [← add_mul,← add_one_mul]
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    simpa [add_comm] using tb (t+1) ht
  have hk : η*e*‖gridR N (z t)‖≤8*e*R := by
    have hh := mul_le_mul hc cap (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
    nlinarith only [mul_le_mul_of_nonneg_left hh ep]
  exact ⟨(CircleVariableGD.grid_increment hη (by omega) hm G hρ hr hu cur along).trans hk,
    (CircleVariableGD.mean_increment hη (by omega) hm G hρ hr hu cur along).trans hk⟩

theorem stopped_tracking (n m T : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η ρ u R : ℝ} (z : State m) (hη : 0≤η) (hc : η≤4)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => k0 1) z)
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hR : ‖gridR (n+1) z‖≤R)
    (linear : ∀ v : EuclideanSpace ℝ (Fin (n+1)), ‖v-η • gramOp (sampledMatrix 1) v‖≤‖v‖)
    (factor : |1-η*gamma (n+1)| ≤ 1)
    (drift : T*(64/sqrt m*R)≤ρ) (err : T*(2*(30*ρ+3*u))≤1/8) :
    |trainedMean (CircleSeedIntegrability.path (n+1) m η) T z -
      reference (n+1) m (stoppedCoefficient n T η) z| ≤ 24*(2*(30*ρ+3*u))*R*T := by
  let N := n+1
  let b := weight 1 n
  let a := 1-η*gamma N
  let r := fun t => gridR N (iterateAt N η z t)
  let f := fun t => CircleFlowMoments.mean (iterateAt N η z t)
  let P := rowOp (fun _ : Fin N => b)
  let U := 8*(2*(30*ρ+3*u))*R
  have D := finite_budget hn hm hη hc T G hρ hr hu hR linear drift err
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
      rw [abs_mul]
      exact (add_le_add (pnorm t (by omega)) ((mul_le_of_le_one_left (abs_nonneg _) factor).trans (ih (by omega)))).trans_eq (by push_cast;ring)
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

end CircleReciprocalTracking
