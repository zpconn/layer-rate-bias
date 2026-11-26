module

public import CirclePositiveSpectrum
public import CircleWeightedStep
import all CircleWeightedStep
import all CircleProjectedStep
import all CircleFiniteDynamics
import all CircleActualTracking
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Tactic

/-! Deterministic movement and interpolation under simultaneous GD with an
arbitrary fixed positive hidden layer rate. -/
@[expose] public section
noncomputable section
namespace CircleWeightedDynamics
open Real MeasureTheory Filter Topology Set CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleGridSpectrum CircleEscapeBridge CircleWeightedStep
open CircleProjectedStep (signedMean)
variable {N m : ℕ}
def scale (τ : ℝ) := max 1 τ
private theorem scale_pos (τ : ℝ) : 0<scale τ := zero_lt_one.trans_le (le_max_left _ _)

def rms (τ η : ℝ) (N : ℕ) (z : State m) (t : ℕ) := ‖gridR N (iterate τ η N z t)‖
def budget (τ η : ℝ) (N : ℕ) (z : State m) (t : ℕ) := η*∑ j∈Finset.range t,rms τ η N z j
def learnerMean (τ η : ℝ) (N : ℕ) (z : State m) (t : ℕ) := CircleFlowMoments.mean (iterate τ η N z t)

theorem budget_succ (τ η : ℝ) (N : ℕ) (z : State m) (t : ℕ) :
    budget τ η N z (t+1)=budget τ η N z t+η*rms τ η N z t := by simp [budget,Finset.sum_range_succ,mul_add]

structure Bounds (N : ℕ) [NeZero N] (τ b ρ R g v : ℝ) (z : State m) : Prop where
  residual : ‖gridR N z‖≤R
  energy : meanEnergy z≤4
  gridMargin : ∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ
  angular : angularMargin z ρ≤6*ρ
  gram : ∀ i j : Fin N, |gridGram τ z (startGates z) i j-sampledMatrix τ i j|≤g
  signed : ∀ i : Fin N, |populationRow τ z (startGates z) i - b*((∑ j : Fin N, gridGram τ z (startGates z) j i)/N)|≤v

private theorem drift36 {ρ E g h : ℝ} (τ : ℝ) (p : 0≤ρ) (hr : ρ≤1) (em : E≤4) (gm : g≤6*ρ) (hm : h≤6*ρ) :
    scale τ*((4*ρ+2*ρ^2)*E+g+h) ≤ scale τ*(36*ρ) :=
  mul_le_mul_of_nonneg_left (by simpa only [one_mul] using CircleFiniteDynamics.drift36 p hr em gm hm) (scale_pos τ).le

private theorem grid_motion [NeZero N] {τ : ℝ} (hp : 0≤τ) {b ρ R g v : ℝ} {z v₀ : State m} (hm : 0<m) (p : 0≤ρ) (hr : ρ≤1)
    (G : Bounds N τ b ρ R g v z) (cur : Tube ρ z v₀) (s : ℝ) (ins : Tube ρ z (segment τ N v₀ s))
    (i j : Fin N) :
    |mixedRow τ N v₀ (circleInput N i) s j-gridGram τ z (startGates z) i j|≤scale τ*(36*ρ) :=
  (entry_drift hm (le_max_left 1 τ) ((abs_of_nonneg hp).le.trans (le_max_right _ _)) p
    (grid_unit i) (grid_unit j) ins cur (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)).trans
      (drift36 τ p hr G.energy (G.gridMargin _) (G.gridMargin _))

private theorem signed_bound [NeZero N] {τ : ℝ} (hp : 0≤τ) {b ρ R g v : ℝ} {z w : State m} (hn : 0<N) (hm : 0<m) (p : 0≤ρ) (hr : ρ≤1)
    (hb : 0≤b) (G : Bounds N τ b ρ R g v z) (cur : Tube ρ z w) (s : ℝ) (ins : Tube ρ z (segment τ N w s))
    (j : Fin N) : |signedRow τ N b w s j| ≤ v+(1+b)*(scale τ*(36*ρ)) := by
  let A := gridGram (N:=N) τ z (startGates z)
  let J (i : Fin N) := mixedRow τ N w (circleInput N i) s j
  let q := meanEntry τ (segment τ N w s) w (circleInput N j) (startGates w j)
  let q₀ := populationRow τ z (startGates z) j
  have mt : |q-q₀|≤scale τ*(36*ρ) := (angular_entry_drift hm (le_max_left 1 τ)
    ((abs_of_nonneg hp).le.trans (le_max_right _ _)) p (grid_unit j) ins cur (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _)).trans (drift36 τ p hr G.energy G.angular (G.gridMargin _))
  have gt : |((∑ i,J i)-(∑ i,A i j))/(N:ℝ)|≤scale τ*(36*ρ) := by
    rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N),div_le_iff₀ (Nat.cast_pos.mpr hn),←Finset.sum_sub_distrib]
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => grid_motion hp hm p hr G cur s ins i j))).trans_eq (by simp;ring)
  have init : |q₀-b*((∑ i,A i j)/N)|≤v := by
    exact G.signed j
  change |q-b*((∑ i,J i)/N)|≤_
  rw [show q-b*((∑ i,J i)/N)=(q₀-b*((∑ i,A i j)/N))+((q-q₀)-b*(((∑ i,J i)-(∑ i,A i j))/N)) by ring]
  have bt : |b*(((∑ i,J i)-(∑ i,A i j))/N)|≤b*(scale τ*(36*ρ)) := by
    rw [abs_mul,abs_of_nonneg hb];exact mul_le_mul_of_nonneg_left gt hb
  exact (abs_add_le ..).trans ((add_le_add init ((abs_sub ..).trans (add_le_add mt bt))).trans_eq (by ring))

private theorem move {τ : ℝ} (hp : 0≤τ) (hn : 0<N) {ρ s : ℝ} {z w : State m} (s0 : 0≤s) (tube : Tube ρ z w) (small : ρ≤1)
    (j : Fin m) :
    length (segment τ N w s-z) j ≤ length (w-z) j+s*((2*scale τ)/sqrt m*‖gridR N w‖*length z j) := by
  have eq : length (segment τ N w s-w) j = s*length (direction τ N w) j := by
    simp only [CircleActualTracking.length_entity]
    have vec : (WithLp.toLp 2 (fun k : Fin 3 => (segment τ N w s-w) (j,k)) : EuclideanSpace ℝ (Fin 3)) =
      s • WithLp.toLp 2 (fun k : Fin 3 => direction τ N w (j,k)) := by ext k;change w (j,k)+s*direction τ N w (j,k)-w (j,k)=s*direction τ N w (j,k);ring
    rw [vec,norm_smul,Real.norm_eq_abs,abs_of_nonneg s0]
  have tri : length (segment τ N w s-z) j ≤ length (segment τ N w s-w) j+length (w-z) j := by
    simp only [CircleActualTracking.length_entity]
    exact norm_sub_le_norm_sub_add_norm_sub
      (WithLp.toLp 2 (fun k : Fin 3 => segment τ N w s (j,k)) : EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 (fun k : Fin 3 => w (j,k))) (WithLp.toLp 2 (fun k : Fin 3 => z (j,k)))
  have b := (current_length tube j).trans (mul_le_mul_of_nonneg_right (by linarith : 1+ρ≤2) (sqrt_nonneg _))
  have c := (CircleWeightedStep.direction_le τ hp hn w j).trans ((mul_le_mul_of_nonneg_left b (by exact mul_nonneg (scale_pos τ).le (by positivity) : 0≤scale τ*(‖gridR N w‖/sqrt m))).trans_eq
    (by ring : _=(2*scale τ)/sqrt m*‖gridR N w‖*length z j))
  rw [eq] at tri
  exact tri.trans ((add_le_add (mul_le_mul_of_nonneg_left c s0) le_rfl).trans_eq (add_comm _ _))

private theorem bootstrap {N m : ℕ} [NeZero N] (hN : 3≤N) (hm : 0<m) (z : Seed m)
    {τ η b ρ R g v k : ℝ} (hp : 0<τ) (hη : 0<η) (contract : ∀ x : EuclideanSpace ℝ (Fin N),
      ‖x-η • gramOp (sampledMatrix τ) x‖ ≤ (1-η*(τ/(π*(N:ℝ))^2))*‖x‖) (hρ : 0≤ρ) (hr : ρ≤1) (hg : 0≤g) (_hk : 0<k) (hk1 : η*k≤1)
    (G : Bounds N τ b ρ R g v z)
    (cash : (2*scale τ)/sqrt m*R≤ρ*k) (gap : (scale τ*(36*ρ)+g) ≤ τ/(π*(N:ℝ))^2-k) :
    ∀ t, rms τ η N z t≤(1-η*k)^t*R ∧ Tube ρ z (iterate τ η N z t) ∧
      ∀ s ∈ Set.Icc (0:ℝ) η, Tube ρ z (segment τ N (iterate τ η N z t) s) := by
  let q := 1-η*k
  let w := iterate τ η N z
  have sc := (scale_pos τ).le
  have qp : 0≤q := sub_nonneg.mpr hk1
  let P (t : ℕ) := rms τ η N z t≤q^t*R ∧ ∀ j, length (w t-z) j≤ρ*(1-q^t)*length z j
  have tube (t : ℕ) (H : P t) : Tube ρ z (w t) := fun j => (H.2 j).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg hρ (pow_nonneg qp t)] : ρ*(1-q^t)≤ρ) (sqrt_nonneg _))
  have next (t : ℕ) (H : P t) (s : ℝ) (hs : s∈Set.Icc (0:ℝ) η) (j : Fin m) :
      length (segment τ N (w t) s-z) j≤ρ*(1-q^(t+1))*length z j := by
    have mv := move hp.le (by omega : 0<N) hs.1 (tube t H) hr j
    have d := (mul_le_mul_of_nonneg_left H.1 (show 0≤(2*scale τ)/sqrt (m:ℝ) by positivity)).trans
      ((by ring : (2*scale τ)/sqrt (m:ℝ)*(q^t*R)=((2*scale τ)/sqrt m*R)*q^t).le.trans (mul_le_mul_of_nonneg_right cash (pow_nonneg qp t)))
    have c := mul_le_mul hs.2 (mul_le_mul_of_nonneg_right d (show 0≤length z j from sqrt_nonneg _))
      (by unfold rms length;positivity) hη.le
    exact mv.trans ((add_le_add (H.2 j) c).trans_eq (by rw [pow_succ];dsimp [q];ring))
  have along t (H : P t) s (hs : s∈Set.Icc (0:ℝ) η) : Tube ρ z (segment τ N (w t) s) :=
    fun j => (next t H s hs j).trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_nonneg hρ (pow_nonneg qp (t+1))] : ρ*(1-q^(t+1))≤ρ) (sqrt_nonneg _))
  have p (t : ℕ) : P t := by
    induction t with
    | zero => exact ⟨by simpa [rms,iterate] using G.residual,fun j => by simp [w,iterate,length]⟩
    | succ t ih =>
      refine ⟨?_,next t ih η ⟨hη.le,le_rfl⟩⟩
      let v := gridR N (w t)
      let v' := gridR N (w (t+1))
      let u' := v-η • gramOp (sampledMatrix τ) v
      have defect : ‖v'-u'‖ ≤ η*((scale τ*(36*ρ)+g))*‖v‖ := by
        apply grid_defect τ hη.le (by omega) _ (by positivity)
        intro i s hs j
        exact (abs_sub_le _ _ _).trans (add_le_add (grid_motion hp.le hm hρ hr G (tube t ih) s (along t ih s hs) i j) (G.gram i j))
      have tri := norm_sub_le_norm_sub_add_norm_sub v' u' 0
      simp only [sub_zero] at tri
      have h : ‖v'‖ ≤ q*‖v‖ := tri.trans ((add_le_add defect (contract v)).trans
        (by dsimp [q];nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gap hη.le) (norm_nonneg v)]))
      exact h.trans ((mul_le_mul_of_nonneg_left ih.1 qp).trans_eq (by ring))
  exact fun t => ⟨(p t).1,tube t (p t),along t (p t)⟩

/-- Geometric decay confines every parameter coordinate to a convergent path.
The limiting network interpolates the training labels. -/
theorem parameters_converge {τ η k ρ R : ℝ} (hp : 0≤τ) (hn : 0<N) (z : State m)
    (hη : 0<η) (hk : 0<k) (hq : 0≤1-η*k) (hr : ρ≤1)
    (decay : ∀ t, rms τ η N z t ≤ (1-η*k)^t*R)
    (tube : ∀ t, Tube ρ z (iterate τ η N z t)) :
    ∃ w : State m, Tendsto (iterate τ η N z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  let q := 1-η*k
  let w := iterate τ η N z
  have qlt : q<1 := sub_lt_self _ (mul_pos hη hk)
  have coord (u : State m) (p : Coord m) : |u p|≤length u p.1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    simp only [sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),sq_abs]
    exact Finset.single_le_sum (fun i (_ : i∈Finset.univ) => sq_nonneg (u (p.1,i))) (Finset.mem_univ p.2)
  have limits (p : Coord m) : ∃ v : ℝ, Tendsto (fun t => w t p) atTop (𝓝 v) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_geometric q (η*(scale τ*(R/sqrt m))*(2*length z p.1)) qlt
    intro t
    rw [Real.dist_eq, abs_sub_comm]
    change |w t p+η*direction τ N (w t) p-w t p|≤_
    rw [add_sub_cancel_left,abs_mul,abs_of_pos hη]
    have a := (current_length (tube t) p.1).trans (mul_le_mul_of_nonneg_right
      (by linarith only [hr] : 1+ρ≤2) (sqrt_nonneg _))
    have c := (coord _ p).trans ((CircleWeightedStep.direction_le τ hp hn (w t) p.1).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (decay t) (sqrt_nonneg _)) (scale_pos τ).le) a (sqrt_nonneg _)
        (mul_nonneg (scale_pos τ).le (div_nonneg ((norm_nonneg _).trans (decay t)) (sqrt_nonneg _)))))
    exact (mul_le_mul_of_nonneg_left c hη.le).trans_eq (by dsimp only [q,scale];ring)
  choose v hv using limits
  have lim : Tendsto w atTop (𝓝 v) := tendsto_pi_nhds.mpr hv
  have toZero : Tendsto (fun t => ‖gridR N (w t)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) decay
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq qlt).mul_const R
  have cont : Continuous (fun u : State m => ‖gridR N u‖^2) := by
    simp_rw [gridR,rmsCoordinates_norm_sq]
    unfold CircleFlowPath.residual output pre
    fun_prop
  have eq := tendsto_nhds_unique ((cont.tendsto v).comp lim) (toZero.pow 2)
  refine ⟨v,lim,?_⟩
  change ‖gridR N v‖^2=(0:ℝ)^2 at eq
  simpa only [sq_eq_zero_iff,zero_pow (by decide : 2≠0)] using eq

/-- Kernel confinement and the projected population comparison for every
integer time. The positive limiting statement concerns the original GD
parameters, including seeds with zero-length neurons. -/
theorem trajectory_of_contraction [NeZero N] (hN : 3≤N) (hm : 0<m) (z : Seed m)
    {τ η b ρ R g v k : ℝ} (hp : 0<τ) (hη : 0<η) (contract : ∀ x : EuclideanSpace ℝ (Fin N),
      ‖x-η • gramOp (sampledMatrix τ) x‖ ≤ (1-η*(τ/(π*(N:ℝ))^2))*‖x‖) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hg : 0≤g) (hv : 0≤v) (hk : 0<k) (hk1 : η*k≤1) (G : Bounds N τ b ρ R g v z)
    (cash : (2*scale τ)/sqrt m*R≤ρ*k) (gap : scale τ*(36*ρ)+g≤τ/(π*(N:ℝ))^2-k) :
    (∀ t, rms τ η N z t≤(1-η*k)^t*R ∧ budget τ η N z t≤R/k ∧
      |learnerMean τ η N z t-reference N m b z| ≤ b*rms τ η N z t+(v+(1+b)*(scale τ*(36*ρ)))*(R/k)) ∧
    ∃ w : State m, Tendsto (iterate τ η N z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  let e := v+(1+b)*(scale τ*(36*ρ))
  let w := iterate τ η N z
  have sc := (scale_pos τ).le
  have ep : 0≤e := by dsimp [e];positivity
  have rp := (norm_nonneg _).trans G.residual
  have qp := sub_nonneg.mpr hk1
  have path := bootstrap hN hm z hp hη contract hρ hr hg hk hk1 G cash gap
  have area (t : ℕ) : budget τ η N z t≤R/k := by
    have h (t : ℕ) : k*budget τ η N z t+(1-η*k)^t*R≤R := by
      induction t with
      | zero => simp [budget]
      | succ t ih =>
        rw [budget_succ,pow_succ]
        have c := mul_le_mul_of_nonneg_left (path t).1 (mul_nonneg hη.le hk.le)
        linarith only [ih,c]
    apply (le_div_iff₀ hk).2
    linarith only [h t,mul_nonneg (pow_nonneg qp t) rp]
  have obs (t : ℕ) : |signedMean N b (w t)-signedMean N b z|≤e*budget τ η N z t := by
    induction t with
    | zero => simp [w,iterate,budget]
    | succ t ih =>
      have inc := signed_increment τ hη.le (by omega : 0<N) hm b (w t) ep
        (fun s hs j => signed_bound hp.le (by omega) hm hρ hr hb G (path t).2.1 s ((path t).2.2 s hs) j)
      exact (abs_sub_le _ (signedMean N b (w t)) _).trans ((add_le_add inc ih).trans_eq
        (by rw [budget_succ];dsimp only [rms,w];ring))
  constructor
  · intro t
    refine ⟨(path t).1,area t,?_⟩
    let P := rowOp (fun _ : Fin N => b)
    have proj := (P.le_opNorm (gridR N (w t))).trans (mul_le_mul_of_nonneg_right
      (rowOp_norm (by omega : 0<N) hb (fun _ => (abs_of_nonneg hb).le)) (norm_nonneg _))
    rw [←actual_reference hN z b]
    change |CircleFlowMoments.mean (w t)-signedMean N b z|≤_
    rw [show CircleFlowMoments.mean (w t)-signedMean N b z=P (gridR N (w t))+(signedMean N b (w t)-signedMean N b z) by unfold signedMean;dsimp only [P];ring]
    exact (abs_add_le ..).trans (add_le_add proj ((obs t).trans (mul_le_mul_of_nonneg_left (area t) ep)))
  · exact parameters_converge hp.le (by omega) z hη hk qp hr (fun t => (path t).1) (fun t => (path t).2.1)

/-- The positive semidefinite step-size regime. -/
theorem trajectory [NeZero N] (hN : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {τ η b ρ R g v k : ℝ} (hp : 0<τ) (hη : 0<η) (stable : η*(1+τ)≤2) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hg : 0≤g) (hv : 0≤v) (hk : 0<k) (hk1 : η*k≤1) (G : Bounds N τ b ρ R g v z)
    (cash : (2*scale τ)/sqrt m*R≤ρ*k) (gap : scale τ*(36*ρ)+g≤τ/(π*(N:ℝ))^2-k) :
    (∀ t, rms τ η N z t≤(1-η*k)^t*R ∧ budget τ η N z t≤R/k ∧
      |learnerMean τ η N z t-reference N m b z| ≤ b*rms τ η N z t+(v+(1+b)*(scale τ*(36*ρ)))*(R/k)) ∧
    ∃ w : State m, Tendsto (iterate τ η N z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  exact trajectory_of_contraction hN hm z hp hη
    (CirclePositiveSpectrum.contraction hN odd τ η hp hη.le stable)
    hb hρ hr hg hv hk hk1 G cash gap

/-- Unit-step GD permits the slow and fast rates on the same training clock. -/
theorem unit_trajectory [NeZero N] (hN : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {τ b ρ R g v k : ℝ} (hp : 0<τ) (hτ : τ≤2) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hg : 0≤g) (hv : 0≤v) (hk : 0<k) (hk1 : (1:ℝ)*k≤1) (G : Bounds N τ b ρ R g v z)
    (cash : (2*scale τ)/sqrt m*R≤ρ*k) (gap : scale τ*(36*ρ)+g≤τ/(π*(N:ℝ))^2-k) :
    (∀ t, rms τ 1 N z t≤(1-(1:ℝ)*k)^t*R ∧ budget τ 1 N z t≤R/k ∧
      |learnerMean τ 1 N z t-reference N m b z| ≤ b*rms τ 1 N z t+(v+(1+b)*(scale τ*(36*ρ)))*(R/k)) ∧
    ∃ w : State m, Tendsto (iterate τ 1 N z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  exact trajectory_of_contraction hN hm z hp zero_lt_one
    (CirclePositiveSpectrum.unit_contraction hN odd τ hp hτ)
    hb hρ hr hg hv hk hk1 G cash gap

end CircleWeightedDynamics
