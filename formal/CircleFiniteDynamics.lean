module

public import CircleNeuronSpeed
public import CircleProjectedStep
import all CircleProjectedStep
import all CircleRateTrajectory
import all CircleDiscreteTracking
import all CircleWidthTracking
import all CircleActualTracking
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Tactic

/-! Deterministic training, arbitrary integer width, and convergence of the
original parameters for the finite-confidence circle theorem. -/
public section
noncomputable section
namespace CircleFiniteDynamics
open Real MeasureTheory Filter Topology Set CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleDiscreteTracking CircleGridSpectrum CircleWidthTracking CircleRateTrajectory CircleProjectedStep CircleEscapeBridge
variable {N m : ℕ}

/-- Width- and confidence-independent deterministic content of the six
initialization tests. Each threshold here is measured on the unscaled row. -/
structure Bounds (N : ℕ) [NeZero N] (b ρ R g v : ℝ) (z : State m) : Prop where
  residual : ‖gridR N z‖≤R
  energy : meanEnergy z≤4
  gridMargin : ∀ i : Fin N, marginMass z ρ (circleInput N i)≤6*ρ
  angular : angularMargin z ρ≤6*ρ
  gram : ∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤g
  signed : ∀ i : Fin N, |CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N i)|≤v

private theorem drift36 {ρ E g h : ℝ} (p : 0≤ρ) (hr : ρ≤1) (em : E≤4) (gm : g≤6*ρ) (hm : h≤6*ρ) :
    1*((4*ρ+2*ρ^2)*E+g+h) ≤ 36*ρ := by
  nlinarith only [mul_le_mul_of_nonneg_left em (by positivity : 0≤4*ρ+2*ρ^2), gm,hm,
    mul_nonneg p (sub_nonneg.mpr hr)]

private theorem grid_motion [NeZero N] {b ρ R g v : ℝ} {z v₀ : State m} (hm : 0<m) (p : 0≤ρ) (hr : ρ≤1)
    (G : Bounds N b ρ R g v z) (cur : Tube ρ z v₀) (s : ℝ) (ins : Tube ρ z (seg N v₀ s))
    (i j : Fin N) :
    |mixedRow N v₀ (circleInput N i) s j-gridGram 1 z (startGates z) i j|≤36*ρ :=
  (entry_drift hm (by norm_num : (1:ℝ)≤1) (by norm_num : |(1:ℝ)|≤1) p
    (grid_unit i) (grid_unit j) ins cur (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _) (fun _ => actualGate_admissible _)).trans
      (drift36 p hr G.energy (G.gridMargin _) (G.gridMargin _))

private theorem signed_bound [NeZero N] {b ρ R g v : ℝ} {z w : State m} (hn : 0<N) (hm : 0<m) (p : 0≤ρ) (hr : ρ≤1)
    (hb : 0≤b) (G : Bounds N b ρ R g v z) (cur : Tube ρ z w) (s : ℝ) (ins : Tube ρ z (seg N w s))
    (j : Fin N) : |signedRow N b w s j| ≤ v+(1+b)*36*ρ := by
  let A := gridGram (N:=N) 1 z (startGates z)
  let J (i : Fin N) := mixedRow N w (circleInput N i) s j
  let q := meanEntry 1 (seg N w s) w (circleInput N j) (startGates w j)
  let q₀ := populationRow 1 z (startGates z) j
  have mt : |q-q₀|≤36*ρ := (angular_entry_drift hm (by norm_num : (1:ℝ)≤1)
    (by norm_num : |(1:ℝ)|≤1) p (grid_unit j) ins cur (fun _ => actualGate_admissible _)
    (fun _ => actualGate_admissible _)).trans (drift36 p hr G.energy G.angular (G.gridMargin _))
  have gt : |((∑ i,J i)-(∑ i,A i j))/(N:ℝ)|≤36*ρ := by
    rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N),div_le_iff₀ (Nat.cast_pos.mpr hn),←Finset.sum_sub_distrib]
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => grid_motion hm p hr G cur s ins i j))).trans_eq (by simp;ring)
  have init : |q₀-b*((∑ i,A i j)/N)|≤v := by
    have h := G.signed j
    rw [CircleSignedRow.mixedRow_eq _ _ hm] at h
    exact h
  change |q-b*((∑ i,J i)/N)|≤_
  rw [show q-b*((∑ i,J i)/N)=(q₀-b*((∑ i,A i j)/N))+((q-q₀)-b*(((∑ i,J i)-(∑ i,A i j))/N)) by ring]
  have bt : |b*(((∑ i,J i)-(∑ i,A i j))/N)|≤b*(36*ρ) := by
    rw [abs_mul,abs_of_nonneg hb];exact mul_le_mul_of_nonneg_left gt hb
  exact (abs_add_le ..).trans ((add_le_add init ((abs_sub ..).trans (add_le_add mt bt))).trans_eq (by ring))

private theorem move {ρ s : ℝ} {z w : State m} (s0 : 0≤s) (tube : Tube ρ z w) (small : ρ≤1)
    (speed : ∀ j, length (direction N w) j ≤ ‖gridR N w‖/sqrt m*length w j) (j : Fin m) :
    length (seg N w s-z) j ≤ length (w-z) j+s*(2/sqrt m*‖gridR N w‖*length z j) := by
  have eq : length (seg N w s-w) j = s*length (direction N w) j := by
    simp only [CircleActualTracking.length_entity]
    have vec : (WithLp.toLp 2 (fun k : Fin 3 => (seg N w s-w) (j,k)) : EuclideanSpace ℝ (Fin 3)) =
      s • WithLp.toLp 2 (fun k : Fin 3 => direction N w (j,k)) := by ext k;change w (j,k)+s*direction N w (j,k)-w (j,k)=s*direction N w (j,k);ring
    rw [vec,norm_smul,Real.norm_eq_abs,abs_of_nonneg s0]
  have tri : length (seg N w s-z) j ≤ length (seg N w s-w) j+length (w-z) j := by
    simp only [CircleActualTracking.length_entity]
    exact norm_sub_le_norm_sub_add_norm_sub
      (WithLp.toLp 2 (fun k : Fin 3 => seg N w s (j,k)) : EuclideanSpace ℝ (Fin 3))
      (WithLp.toLp 2 (fun k : Fin 3 => w (j,k))) (WithLp.toLp 2 (fun k : Fin 3 => z (j,k)))
  have b := (current_length tube j).trans (mul_le_mul_of_nonneg_right (by linarith : 1+ρ≤2) (sqrt_nonneg _))
  have c := (speed j).trans ((mul_le_mul_of_nonneg_left b (by positivity : 0≤‖gridR N w‖/sqrt m)).trans_eq
    (by ring : _=2/sqrt m*‖gridR N w‖*length z j))
  rw [eq] at tri
  exact tri.trans ((add_le_add (mul_le_mul_of_nonneg_left c s0) le_rfl).trans_eq (add_comm _ _))

private theorem bootstrap {N m : ℕ} [NeZero N] (hN : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {η b ρ R g v k : ℝ} (hη : 0<η) (hc : η≤1) (hρ : 0≤ρ) (hr : ρ≤1) (hg : 0≤g) (hk : 0<k) (hk1 : k≤1)
    (G : Bounds N b ρ R g v z)
    (cash : 2/sqrt m*R≤ρ*k) (gap : (36*ρ+g) ≤ 1/(π*(N:ℝ))^2-k) :
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
    have mv := move hs.1 (tube t H) hr (CircleNeuronSpeed.direction_le (by omega : 0<N) (w t)) j
    have d := (mul_le_mul_of_nonneg_left H.1 (show 0≤2/sqrt (m:ℝ) by positivity)).trans
      ((by ring : 2/sqrt (m:ℝ)*(q^t*R)=(2/sqrt m*R)*q^t).le.trans (mul_le_mul_of_nonneg_right cash (pow_nonneg qp t)))
    have c := mul_le_mul hs.2 (mul_le_mul_of_nonneg_right d (show 0≤length z j from sqrt_nonneg _))
      (by unfold rms length;positivity) hη.le
    exact mv.trans ((add_le_add (H.2 j) c).trans_eq (by rw [pow_succ];dsimp [q];ring))
  have along t (H : P t) s (hs : s∈Set.Icc (0:ℝ) η) : Tube ρ z (CircleDiscreteTracking.seg N (w t) s) :=
    fun j => (next t H s hs j).trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_nonneg hρ (pow_nonneg qp (t+1))] : ρ*(1-q^(t+1))≤ρ) (sqrt_nonneg _))
  have p (t : ℕ) : P t := by
    induction t with
    | zero => exact ⟨by simpa [rms,iterateAt] using G.residual,fun j => by simp [w,iterateAt,length]⟩
    | succ t ih =>
      refine ⟨?_,next t ih η ⟨hη.le,le_rfl⟩⟩
      let v := gridR N (w t)
      let v' := gridR N (w (t+1))
      let u' := v-η • gramOp (sampledMatrix 1) v
      have defect : ‖v'-u'‖ ≤ η*((36*ρ+g))*‖v‖ := by
        apply grid_defect hη.le (by omega) _ (by positivity)
        intro i s hs j
        exact (abs_sub_le _ _ _).trans (add_le_add (grid_motion hm hρ hr G (tube t ih) s (along t ih s hs) i j) (G.gram i j))
      have tri := norm_sub_le_norm_sub_add_norm_sub v' u' 0
      simp only [sub_zero] at tri
      have h : ‖v'‖ ≤ q*‖v‖ := tri.trans ((add_le_add defect (CircleRateTrajectory.contractionAt hN odd hη.le hc v)).trans
        (by dsimp [q];nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gap hη.le) (norm_nonneg v)]))
      exact h.trans ((mul_le_mul_of_nonneg_left ih.1 qp).trans_eq (by ring))
  exact fun t => ⟨(p t).1,tube t (p t),along t (p t)⟩

/-- Geometric decay confines every parameter coordinate to a convergent path.
The limiting network interpolates the training labels. -/
theorem parameters_converge {η k ρ R : ℝ} (hn : 0<N) (z : State m)
    (hη : 0<η) (hk : 0<k) (hq : 0≤1-η*k) (hr : ρ≤1)
    (decay : ∀ t, rms η N z t ≤ (1-η*k)^t*R)
    (tube : ∀ t, Tube ρ z (iterateAt N η z t)) :
    ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  let q := 1-η*k
  let w := iterateAt N η z
  have qlt : q<1 := sub_lt_self _ (mul_pos hη hk)
  have coord (u : State m) (p : Coord m) : |u p|≤length u p.1 := by
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    simp only [sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),sq_abs]
    exact Finset.single_le_sum (fun i (_ : i∈Finset.univ) => sq_nonneg (u (p.1,i))) (Finset.mem_univ p.2)
  have limits (p : Coord m) : ∃ v : ℝ, Tendsto (fun t => w t p) atTop (𝓝 v) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_geometric q (η*(R/sqrt m)*(2*length z p.1)) qlt
    intro t
    rw [Real.dist_eq, abs_sub_comm]
    change |w t p+η*direction N (w t) p-w t p|≤_
    rw [add_sub_cancel_left,abs_mul,abs_of_pos hη]
    have a := (current_length (tube t) p.1).trans (mul_le_mul_of_nonneg_right
      (by linarith only [hr] : 1+ρ≤2) (sqrt_nonneg _))
    have c := (coord _ p).trans ((CircleNeuronSpeed.direction_le hn (w t) p.1).trans
      (mul_le_mul (div_le_div_of_nonneg_right (decay t) (sqrt_nonneg _)) a (sqrt_nonneg _)
        (div_nonneg ((norm_nonneg _).trans (decay t)) (sqrt_nonneg _))))
    exact (mul_le_mul_of_nonneg_left c hη.le).trans_eq (by dsimp only [q];ring)
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
theorem trajectory [NeZero N] (hN : 3≤N) (hm : 0<m) (odd : Odd N) (z : Seed m)
    {η b ρ R g v k : ℝ} (hη : 0<η) (hc : η≤1) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1)
    (hg : 0≤g) (hv : 0≤v) (hk : 0<k) (hk1 : k≤1) (G : Bounds N b ρ R g v z)
    (cash : 2/sqrt m*R≤ρ*k) (gap : 36*ρ+g≤1/(π*(N:ℝ))^2-k) :
    (∀ t, rms η N z t≤(1-η*k)^t*R ∧ budget η N z t≤R/k ∧
      |learnerMean η N z t-reference N m b z| ≤ b*rms η N z t+(v+(1+b)*36*ρ)*(R/k)) ∧
    ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  let e := v+(1+b)*36*ρ
  let w := iterateAt N η z
  have ep : 0≤e := by dsimp [e];positivity
  have rp := (norm_nonneg _).trans G.residual
  have qp := sub_nonneg.mpr ((mul_le_of_le_one_left hk.le hc).trans hk1)
  have path := bootstrap hN hm odd z hη hc hρ hr hg hk hk1 G cash gap
  have area (t : ℕ) : budget η N z t≤R/k := by
    have h (t : ℕ) : k*budget η N z t+(1-η*k)^t*R≤R := by
      induction t with
      | zero => simp [budget]
      | succ t ih =>
        rw [budget_succ,pow_succ]
        have c := mul_le_mul_of_nonneg_left (path t).1 (mul_nonneg hη.le hk.le)
        linarith only [ih,c]
    apply (le_div_iff₀ hk).2
    linarith only [h t,mul_nonneg (pow_nonneg qp t) rp]
  have obs (t : ℕ) : |signedMean N b (w t)-signedMean N b z|≤e*budget η N z t := by
    induction t with
    | zero => simp [w,iterateAt,budget]
    | succ t ih =>
      have inc := signed_increment hη.le (by omega : 0<N) hm b (w t) ep
        (fun s hs j => signed_bound (by omega) hm hρ hr hb G (path t).2.1 s ((path t).2.2 s hs) j)
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
  · exact parameters_converge (by omega) z hη hk qp hr (fun t => (path t).1) (fun t => (path t).2.1)

end CircleFiniteDynamics
