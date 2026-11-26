module

public import CircleEarlyWidth
public import CircleFiniteDynamics
import all CircleFiniteDynamics
import all CircleProjectedStep
import all CircleWidthTracking
import all CircleRateTrajectory
import all CircleActualTracking
import all CircleKernelGD
import all CircleSeedIntegrability
import Mathlib.Tactic

/-! The arbitrary-confidence logarithmic stopping bound for the trained
whole-circle mean under simultaneous gradient descent. -/
public section
noncomputable section
namespace CircleEarlyStopping
open Real MeasureTheory Set CircleEscapeBridge CircleFlowPath CircleTangentDrift CircleActualTracking
  CircleWidthTracking CircleDiscreteTracking CircleGridSpectrum CircleSpectrum CircleRateTrajectory
  CircleProjectedStep CircleFiniteDynamics CircleKernelGD CircleFiniteConfidence
variable {N m : ℕ} [NeZero N]
set_option maxHeartbeats 800000

private theorem early_path (hn : 3≤N) (hm : 0<m) (odd : Odd N) (T : ℕ) (z : Seed m)
    {η b ρ R g v : ℝ} (hη : 0<η) (hc : η≤1) (hρ : 0≤ρ) (hr : ρ≤1) (hg : 0≤g)
    (G : Bounds N b ρ R g v z) (cash : T*(4*η*R/sqrt m)≤ρ) (small : T*(η*(36*ρ+g))≤log 2) :
    let w := iterateAt N η z
    (∀ t≤T, ‖gridR N (w t)‖≤2*R) ∧ ∀ t<T, Tube ρ z (w t) ∧
      (∀ s ∈ Icc (0:ℝ) η, Tube ρ z (seg N (w t) s)) ∧
      ‖gridR N (w (t+1))-(gridR N (w t)-η • gramOp (sampledMatrix 1) (gridR N (w t)))‖≤η*(36*ρ+g)*(2*R) := by
  intro w
  let e := 36*ρ+g
  let a := 1+η*e
  let d := 4*η*R/sqrt m
  have rp := (norm_nonneg _).trans G.residual
  have ep : 0≤e := by dsimp [e];positivity
  have ap : 0≤a := by dsimp [a];positivity
  have dp : 0≤d := by dsimp [d];positivity
  have growth (t : ℕ) (ht : t≤T) : a^t≤2 := by
    have h := pow_le_pow_left₀ ap (show a≤exp (η*e) by dsimp [a];linarith [add_one_le_exp (η*e)]) t
    rw [←exp_nat_mul] at h
    exact h.trans ((exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (mul_nonneg hη.le ep)).trans small)).trans_eq (exp_log (by norm_num)))
  let P (t : ℕ) := ‖gridR N (w t)‖≤a^t*R ∧ ∀ j, length (w t-z) j≤(t*d)*length z j
  have room (t : ℕ) (ht : t≤T) : (t:ℝ)*d≤ρ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) dp).trans cash
  have bound (t : ℕ) (ht : t≤T) (H : P t) : ‖gridR N (w t)‖≤2*R :=
    H.1.trans (mul_le_mul_of_nonneg_right (growth t ht) rp)
  have tube (t : ℕ) (ht : t≤T) (H : P t) : Tube ρ z (w t) := fun j =>
    (H.2 j).trans (mul_le_mul_of_nonneg_right (room t ht) (sqrt_nonneg _))
  have next (t : ℕ) (ht : t<T) (H : P t) (s : ℝ) (hs : s∈Icc (0:ℝ) η) (j : Fin m) :
      length (seg N (w t) s-z) j≤((t+1:ℕ)*d)*length z j := by
    have mv := CircleFiniteDynamics.move hs.1 (tube t ht.le H) hr (CircleNeuronSpeed.direction_le (by omega : 0<N) (w t)) j
    have dn : s*(2/sqrt m*‖gridR N (w t)‖*length z j)≤d*length z j := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul hs.2 (bound t ht.le H) (norm_nonneg _) hη.le) (show 0≤2/sqrt (m:ℝ) by positivity)) (show 0≤length z j from sqrt_nonneg _)
      convert h using 1 <;> (try dsimp only [d]) <;> ring
    exact mv.trans ((add_le_add (H.2 j) dn).trans_eq (by push_cast;ring))
  have along (t : ℕ) (ht : t<T) (H : P t) (s : ℝ) (hs : s∈Icc (0:ℝ) η) : Tube ρ z (seg N (w t) s) := fun j =>
    (next t ht H s hs j).trans (mul_le_mul_of_nonneg_right (room _ ht) (sqrt_nonneg _))
  have defect (t : ℕ) (ht : t<T) (H : P t) :
      ‖gridR N (w (t+1))-(gridR N (w t)-η • gramOp (sampledMatrix 1) (gridR N (w t)))‖≤η*e*‖gridR N (w t)‖ := by
    apply grid_defect hη.le (by omega) _ ep
    intro i s hs j
    exact (abs_sub_le _ _ _).trans (add_le_add (grid_motion hm hρ hr G (tube t ht.le H) s (along t ht H s hs) i j) (G.gram i j))
  have run (t : ℕ) (ht : t≤T) : P t := by
    induction t with
    | zero => exact ⟨by simpa [w,iterateAt] using G.residual,fun _ => by simp [w,iterateAt,length]⟩
    | succ t ih =>
      have H := ih (by omega)
      refine ⟨?_,next t ht H η ⟨hη.le,le_rfl⟩⟩
      let r := gridR N (w t)
      let r' := gridR N (w (t+1))
      let u := r-η • gramOp (sampledMatrix 1) r
      have tri := norm_sub_le_norm_sub_add_norm_sub r' u 0
      simp only [sub_zero] at tri
      have q : ‖r'‖≤a*‖r‖ := tri.trans ((add_le_add (defect t ht H) (CircleWidthTracking.nonexpansive hn odd hη.le hc r)).trans_eq (by dsimp [a];ring))
      exact q.trans ((mul_le_mul_of_nonneg_left H.1 ap).trans_eq (by ring))
  exact ⟨fun t ht => bound t ht (run t ht),fun t ht => ⟨tube t ht.le (run t ht.le),along t ht (run t ht.le),
    (defect t ht (run t ht.le)).trans (mul_le_mul_of_nonneg_left (bound t ht.le (run t ht.le)) (mul_nonneg hη.le ep))⟩⟩

private theorem projection (hn : 3≤N) (hm : 0<m) (odd : Odd N) (T : ℕ) (z : Seed m)
    {η b ρ R g v : ℝ} (hη : 0<η) (hc : η≤1) (hb : 0≤b) (hρ : 0≤ρ) (hr : ρ≤1) (hg : 0≤g) (hv : 0≤v)
    (G : Bounds N b ρ R g v z) (cash : T*(4*η*R/sqrt m)≤ρ) (small : T*(η*(36*ρ+g))≤log 2) :
    |learnerMean η N z T-reference N m b z| ≤ b*R*(1-η*gamma N)^T +
      2*b*R*(36*ρ+g)/gamma N + (2*η*T*R)*(v+(1+b)*36*ρ) := by
  let w := iterateAt N η z
  let p := rowOp (fun _ : Fin N => b)
  let r := fun t => gridR N (w t)
  let a := 1-η*gamma N
  let e := 36*ρ+g
  let L := 2*b*R*e/gamma N
  let f := v+(1+b)*36*ρ
  have path := early_path hn hm odd T z hη hc hρ hr hg G cash small
  have rp := (norm_nonneg _).trans G.residual
  have gp : 0<gamma N := (show 0<(3:ℝ)/π^2 by positivity).trans_le (gamma_bounds (N:=N)).1
  have ap : 0≤a := sub_nonneg.mpr ((mul_le_of_le_one_left gp.le hc).trans gamma_bounds.2)
  have ep : 0≤e := by dsimp [e];positivity
  have lp : 0≤L := by dsimp [L];positivity
  have fp : 0≤f := by dsimp [f];positivity
  have pbound (x : EuclideanSpace ℝ (Fin N)) : |p x|≤b*‖x‖ := (p.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (rowOp_norm (by omega : 0<N) hb (fun _ => (abs_of_nonneg hb).le)) (norm_nonneg _))
  have proj (t : ℕ) (ht : t≤T) : |p (r t)|≤b*R*a^t+L := by
    induction t with
    | zero => exact (pbound _).trans ((mul_le_mul_of_nonneg_left G.residual hb).trans (by simpa using lp))
    | succ t ih =>
      let U := r t-η • gramOp (sampledMatrix 1) (r t)
      have d := (pbound (r (t+1)-U)).trans (mul_le_mul_of_nonneg_left (path.2 t ht).2.2 hb)
      have eq := gramOp_eigenrow (N:=N) 1 b (by norm_num) (by norm_num) (r t)
      change p (gramOp (sampledMatrix 1) (r t)) = gamma N*p (r t) at eq
      have peq : p U=a*p (r t) := by dsimp only [U,a];rw [map_sub,map_smul,smul_eq_mul,eq];ring
      rw [map_sub,peq] at d
      have tri := abs_sub_le (p (r (t+1))) (a*p (r t)) 0
      simp only [sub_zero,abs_mul,abs_of_nonneg ap] at tri
      apply tri.trans ((add_le_add d (mul_le_mul_of_nonneg_left (ih (by omega)) ap)).trans_eq ?_)
      dsimp only [a,L,e];field_simp;ring
  have tel (t : ℕ) (ht : t≤T) : |signedMean N b (w t)-signedMean N b z| ≤ (2*η*t*R)*f := by
    induction t with
    | zero => simp [w,iterateAt]
    | succ t ih =>
      have step := signed_increment hη.le (by omega : 0<N) hm b (w t) fp
        (fun s hs j => signed_bound (by omega) hm hρ hr hb G (path.2 t ht).1 s ((path.2 t ht).2.1 s hs) j)
      have paid := (mul_le_mul_of_nonneg_left (path.1 t (by omega)) (mul_nonneg hη.le fp))
      exact (abs_sub_le _ (signedMean N b (w t)) _).trans ((add_le_add (step.trans paid) (ih (by omega))).trans_eq (by push_cast;ring))
  rw [←actual_reference hn z b]
  change |CircleFlowMoments.mean (w T)-signedMean N b z|≤_
  rw [show CircleFlowMoments.mean (w T)-signedMean N b z=p (r T)+(signedMean N b (w T)-signedMean N b z) by unfold signedMean;dsimp only [p,r];ring]
  exact (abs_add_le ..).trans (add_le_add (proj T le_rfl) (tel T le_rfl))

/-- The manuscript's early stopping clock pays for the unperturbed constant
mode uniformly at every eligible width. -/
private theorem clock {η δ ε : ℝ} (hn : 3≤N) (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hδ1 : δ<1) (hε : 0<ε) (hε1 : ε<1) :
    let R := CircleEarlyWidth.R δ; let T := CircleEarlyWidth.cap N η δ ε
    0<T ∧ R*(1-η*gamma N)^T ≤ ε/(2*(N:ℝ)^2) := by
  intro R T
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have one : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have gp : 0<gamma N := (show 0<(3:ℝ)/π^2 by positivity).trans_le (gamma_bounds (N:=N)).1
  have ep := mul_pos hη gp
  have R1 : 1≤R := one_le_sqrt.mpr ((le_div_iff₀ hδ).mpr (by linarith))
  have Rp := zero_lt_one.trans_le R1
  let x := 2*R*(N:ℝ)^2/ε
  have x1 : 1<x := (lt_div_iff₀ hε).mpr (by nlinarith only [hε1,one_le_mul_of_one_le_of_one_le R1 (one_le_pow₀ one (n:=2))])
  have xp := zero_lt_one.trans x1
  have time : log x/(η*gamma N) ≤ (T:ℝ) := Nat.le_ceil _
  have tick : 0<(T:ℝ) := (div_pos (log_pos x1) ep).trans_le time
  refine ⟨Nat.cast_pos.mp tick,?_⟩
  have decay := (CircleKernelGD.disc_exp ((mul_le_of_le_one_left gp.le hc).trans gamma_bounds.2) T).trans
    (exp_le_exp.mpr (show -(η*gamma N*(T:ℝ))≤ -log x by linarith only [(div_le_iff₀ ep).mp time]))
  rw [exp_neg,exp_log xp] at decay
  exact (mul_le_mul_of_nonneg_left decay Rp.le).trans_eq (by dsimp only [x];field_simp)

theorem probability (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η δ ε : ℝ} (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hδ1 : δ<1) (hε : 0<ε) (hε1 : ε<1)
    (size : CircleEarlyWidth.width n η δ ε ≤ sqrt m) :
    let N := n+1; let T := CircleEarlyWidth.cap N η δ ε
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ δ ∧ ∀ z∈E,
      |trainedMean (CircleSeedIntegrability.path N m η) T z-reference N m (weight 1 n) z|≤ε/(N:ℝ)^2 := by
  intro N T
  let R := CircleEarlyWidth.R δ
  let A := CircleEarlyWidth.A N η δ ε
  let D := CircleEarlyWidth.D N η δ ε
  let h := gridScale N δ
  let b := weight 1 n
  let v := signedScale N b δ
  let ρ := A/sqrt m
  let P := 2*b*R*(h+36*A)/gamma N+D*(v+36*(1+b)*A)
  have w : max A (max (sqrt (36/δ)) (max (10*((N:ℝ)+1)/(δ*A)) (max
      (η*T*(h+36*A)/log 2) (2*(N:ℝ)^2/ε*P)))) ≤sqrt m := size
  simp only [max_le_iff] at w
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have sm := sqrt_pos.mpr mp
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have rp : 0<R := sqrt_pos.mpr (by positivity)
  have tim := clock (N:=N) hn hη hc hδ hδ1 hε hε1
  have tt : (0:ℝ)<T := Nat.cast_pos.mpr tim.1
  have dp : 0<D := by change 0<2*η*(T:ℝ)*R;positivity
  have ap : 0<A := by change 0<2*D;positivity
  have ru : ρ≤1 := (div_le_one sm).mpr w.1
  have nr := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  have hp : 0≤h := by dsimp [h,gridScale];positivity
  have vp : 0≤v := by
    have d : 0≤6/(N:ℝ)+1-b := by dsimp [b];linarith [div_nonneg (by norm_num : (0:ℝ)≤6) np.le]
    exact mul_nonneg d (sqrt_nonneg _)
  have energy : 36/δ≤m := (sqrt_le_sqrt_iff mp.le).mp w.2.1
  have margins := w.2.2.1
  have inc := (div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mp w.2.2.2.1
  have roomb : (T:ℝ)*(4*η*R/sqrt m)≤ρ := le_of_eq (by dsimp [ρ,A,CircleEarlyWidth.A,CircleEarlyWidth.D,D,T,R];ring)
  have err : (T:ℝ)*(η*(36*ρ+h/sqrt m))≤log 2 := by
    rw [show (T:ℝ)*(η*(36*ρ+h/sqrt m))=(η*T*(h+36*A))/sqrt m by dsimp [ρ];ring]
    apply (div_le_iff₀ sm).mpr
    linarith only [inc]
  have finalb : P/sqrt m≤ε/(2*(N:ℝ)^2) := by
    apply (div_le_div_iff₀ sm (by positivity)).mpr
    have cash := w.2.2.2.2
    have x : (2*(N:ℝ)^2*P)/ε≤sqrt m := by convert cash using 1;ring
    linarith only [(div_le_iff₀ hε).mp x]
  obtain ⟨E,me,conf,test⟩ := six_tests n m hn odd hm δ A hδ hδ1 ap ru energy (by simpa [N] using margins)
  refine ⟨E,me,conf,?_⟩
  intro z hz
  have H := test z hz
  have data : Bounds N b ρ R (h/sqrt m) (v/sqrt m) z := ⟨H.residual,H.energy,H.gridMargin,H.angular,H.gram,H.signed⟩
  have tr := projection hn hm odd T z hη hc nr.1 (div_nonneg ap.le sm.le) ru (div_nonneg hp sm.le) (div_nonneg vp sm.le) data roomb err
  have a0 := sub_nonneg.mpr ((mul_le_of_le_one_left (show 0≤gamma N from (show 0≤(3:ℝ)/π^2 by positivity).trans gamma_bounds.1) hc).trans gamma_bounds.2)
  have pay : b*R*(1-η*gamma N)^T ≤ ε/(2*(N:ℝ)^2) :=
    (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left rp.le nr.2) (pow_nonneg a0 T)).trans tim.2
  have qq : 2*b*R*(36*ρ+h/sqrt m)/gamma N+(2*η*T*R)*(v/sqrt m+(1+b)*36*ρ) = P/sqrt m := by
    dsimp only [P,ρ,D,CircleEarlyWidth.D,T];ring
  have bound : |learnerMean η N z T-reference N m b z|≤ε/(N:ℝ)^2 := tr.trans (by
    rw [add_assoc,qq]
    exact (add_le_add pay finalb).trans_eq (by ring))
  have eq : trainedMean (CircleSeedIntegrability.path N m η) T z=learnerMean η N z T :=
    congrArg (CircleEscape.populationMean (1/sqrt (m:ℝ))) (iterateAt_eq_train N η z T).symm
  rw [eq]
  exact bound

/-- Success probability for the actual paired statistic at the stated
finite horizon and sufficient width. -/
theorem success_probability (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η δ ε : ℝ} (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hδ1 : δ<1) (hε : 0<ε) (hε1 : ε<1)
    (size : CircleEarlyWidth.width n η δ ε ≤ sqrt m) :
    let N := n+1; let T := CircleEarlyWidth.cap N η δ ε
    1-δ ≤ (seedLaw m).real {z | |trainedMean (CircleSeedIntegrability.path N m η) T z-
      reference N m (weight 1 n) z|≤ε/(N:ℝ)^2} := by
  intro N T
  obtain ⟨E,me,pr,good⟩ := probability n m hn odd hm hη hc hδ hδ1 hε hε1 size
  rw [measureReal_compl me,probReal_univ] at pr
  exact (by linarith : 1-δ≤(seedLaw m).real E).trans (measureReal_mono (fun z hz => good z hz))

end CircleEarlyStopping

