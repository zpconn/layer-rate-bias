module

public import CircleDiscreteMoments
public import CircleDiscreteBudget
import all CircleSpectralPathLength
import all CircleGridSpectrum
import all CircleDiscreteTracking
import all CircleKernelGD
import all CircleSharpTracking
import all CircleSharpInitialization
import all CircleActualTracking
import all CircleTangentDrift
import all CircleEscapeBridge
import all CircleSeedIntegrability
import Mathlib.Tactic

/-! A seed-dependent displacement radius for the true simultaneous GD step.
The induction pays for the next segment before using its mixed tangent rows. -/
public section
noncomputable section
namespace CircleSharpGD
open Real Set Finset CircleFlowPath CircleTangentDrift CircleActualTracking CircleDiscreteTracking
open CircleKernelGD CircleSharpTracking CircleSharpInitialization CircleEscapeBridge CircleGridSpectrum CircleSpectrum
variable {N m : ℕ} [NeZero N]

private theorem local_errors {z₀ z : State m} {ρ B : ℝ} (hm : 0<m) (hρ : 0≤ρ) (hr : ρ≤1)
    (energy : meanEnergy z₀≤4) (margin : ∀ i : Fin N, marginMass z₀ ρ (circleInput N i)≤32*ρ)
    (angular : angularMargin z₀ ρ≤32*ρ)
    (Bcap : initialError N m 1 z₀ ≤ B)
    (cur : Tube ρ z₀ z) (segTube : ∀ s∈Set.Icc (0:ℝ) 1, Tube ρ z₀ (seg N z s)) :
    let r := gridR N z
    let r' := gridR N (seg N z 1)
    ‖r'-update N r‖≤(B+234*ρ)*‖r‖ ∧
      |CircleFlowMoments.mean (seg N z 1)-CircleFlowMoments.mean z+rowOp (fun _ => k0 1) r|≤(B+234*ρ)*‖r‖ := by
  intro r r'
  let A := gridGram 1 z₀ (startGates z₀) (N:=N)
  let k := populationRow 1 z₀ (startGates z₀) (N:=N)
  have G : GoodInit 1 ρ (29*ρ) A k z₀ := by
    refine ⟨energy,fun i => (margin i).trans_eq (by ring),angular.trans_eq (by ring),?_,?_⟩ <;>
      intros <;> simp [A,k] <;> linarith
  have gr := grid_increment (NeZero.pos N) hm G hρ hr (by positivity) cur segTube
  have qr := mean_increment (NeZero.pos N) hm G hρ hr (by positivity) cur segTube
  have hp := (initial_operators_le (N:=N) 1 z₀).trans Bcap
  have gA : ‖gramOp A-gramOp (sampledMatrix 1)‖≤B := (le_add_of_nonneg_right (norm_nonneg _)).trans hp
  have gQ : ‖rowOp k-rowOp (fun _ : Fin N => k0 1)‖≤B := (le_add_of_nonneg_left (norm_nonneg _)).trans hp
  have ca := ((gramOp A-gramOp (sampledMatrix 1)).le_opNorm r).trans (mul_le_mul_of_nonneg_right gA (norm_nonneg _))
  have cq := ((rowOp k-rowOp (fun _ : Fin N => k0 1)).le_opNorm r).trans (mul_le_mul_of_nonneg_right gQ (norm_nonneg _))
  constructor
  · have eq : r' - update N r = (r'-(r-gramOp A r)) - (gramOp A r-gramOp (sampledMatrix 1) r) := by
      change r'-(r-gramOp (sampledMatrix 1) r)=(r'-(r-gramOp A r))-(gramOp A r-gramOp (sampledMatrix 1) r)
      abel
    rw [eq]
    exact ((norm_sub_le _ _).trans (add_le_add gr ca)).trans_eq (by dsimp [r];ring)
  · let δ := CircleFlowMoments.mean (seg N z 1)-CircleFlowMoments.mean z
    change |δ+rowOp (fun _ => k0 1) r|≤_
    rw [show δ+rowOp (fun _ : Fin N => k0 1) r = (δ+rowOp k r)-(rowOp k r-rowOp (fun _ => k0 1) r) by ring]
    exact ((abs_sub _ _).trans (add_le_add qr cq)).trans_eq (by dsimp [r];ring)

private def total (f : ℕ → ℝ) (t : ℕ) := ∑ s ∈ range t, f s

private theorem total_succ (f : ℕ→ℝ) (t : ℕ) : total f (t+1)=total f t+f t := sum_range_succ _ _
private theorem total_nn {f : ℕ→ℝ} (h : ∀t,0≤f t) (t : ℕ) : 0≤total f t := sum_nonneg (fun i _ => h i)
private theorem total_mono {f : ℕ→ℝ} (h : ∀t,0≤f t) {t T : ℕ} (ht : t≤T) :
    total f t≤total f T := sum_le_sum_of_subset_of_nonneg (range_mono ht) (fun i _ _ => h i)

private theorem paid_next {R D F : ℕ→ℝ} {gap e U : ℝ} {t : ℕ}
    (gpos : 0<gap) (hu : gap≤1) (he : 0≤e) (small : 2*e≤gap)
    (hD : ∀ s, 0≤D s) (hR : ∀s,0≤R s) (tri : ∀ s, R s≤F s+D s)
    (bal : D t+gap*total D t≤e*total R t) (cap : total F (t+1)≤U) :
    total R (t+1)≤2*U := by
  have q : gap*total D (t+1)≤e*total R (t+1) := by
    rw [total_succ,total_succ]
    nlinarith only [bal,mul_le_of_le_one_left (hD t) hu,mul_nonneg he (hR t)]
  have r : total R (t+1)≤total F (t+1)+total D (t+1) := by
    unfold total;rw [←sum_add_distrib];exact sum_le_sum (fun s _ => tri s)
  have x := (mul_le_mul_of_nonneg_left r gpos.le).trans_eq (mul_add _ _ _)
  have y := mul_le_mul_of_nonneg_left cap gpos.le
  have z := mul_le_mul_of_nonneg_right small (total_nn hR (t+1))
  exact (mul_le_mul_iff_right₀ gpos).mp (by nlinarith only [x,q,y,z])

/-- Endpoints are compared with the kernel iterate using the sum of frozen
residual norms through the requested stopping time, without a worst-mode time
factor in the error. -/
theorem sharp_stop (n m T : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m) (z : State m)
    (ρ B U : ℝ) (hρ : 0≤ρ) (hr : ρ≤1) (hB : 0≤B) (hU : 0≤U)
    (energy : meanEnergy z≤4) (margin : ∀ i : Fin (n+1), marginMass z ρ (circleInput (n+1) i)≤32*ρ)
    (angular : angularMargin z ρ≤32*ρ) (Bcap : initialError (n+1) m 1 z ≤ B)
    (small : 2*(B+234*ρ)≤1/(π*((n+1:ℕ):ℝ))^2) (budget : (8/sqrt m)*(2*U)≤ρ)
    (area : (∑ s ∈ range T, ‖((update (n+1))^s) (gridR (n+1) z)‖)≤U) :
    |trainedMean (CircleSeedIntegrability.path (n+1) m 1) T z -
      reference (n+1) m (stoppedWeight n T) z| ≤ 6*(B+234*ρ)*U := by
  let N := n+1
  let W := update N
  let K := gramOp (sampledMatrix (N:=N) 1)
  let P := rowOp (fun _ : Fin N => weight 1 n)
  let r (t : ℕ) := gridR N (iterate N z t)
  let f (t : ℕ) := (W^t) (r 0)
  let y (t : ℕ) := CircleFlowMoments.mean (iterate N z t)
  let R (t : ℕ) := ‖r t‖
  let F (t : ℕ) := ‖f t‖
  let D (t : ℕ) := ‖r t-f t‖
  let e := B+234*ρ
  let gap := 1/(π*(N:ℝ))^2
  let d := 8/sqrt (m:ℝ)
  have gpos : 0<gap := by dsimp [gap,N];positivity
  have hu : gap≤1 := CircleKernelGD.gap_le_one hn
  have de : 0≤d := by dsimp [d]; positivity
  have he : 0≤e := by dsimp [e];positivity
  have tri (s : ℕ) : R s≤F s+D s := by
    have h := norm_sub_le_norm_sub_add_norm_sub (r s) (f s) 0
    simpa only [sub_zero,add_comm] using h
  have Pcap (v : EuclideanSpace ℝ (Fin N)) : |P v|≤‖v‖ :=
    (P.le_opNorm v).trans ((mul_le_mul_of_nonneg_right (rowOp_norm (NeZero.pos N) zero_le_one
      (fun _ => weight_abs_le_one n 1 (by norm_num))) (norm_nonneg _)).trans_eq (one_mul _))
  have acc (t : ℕ) (ltT : t≤T) :
      (∀ j, length (iterate N z t-z) j≤d*total R t*length z j) ∧
      D t+gap*total D t≤e*total R t ∧ |y t-P (r t)-(y 0-P (r 0))|≤2*e*total R t := by
    induction t with
    | zero =>
      simp [iterate,total,D,f,R,r,y,length]
    | succ t ih =>
      obtain ⟨disp,bal,obs⟩ := ih (by omega)
      let c := iterate N z t
      have cap : total R (t+1)≤2*U := paid_next gpos hu he small (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        tri bal ((total_mono (f:=F) (fun _ => norm_nonneg _) ltT).trans area)
      have money : d*total R (t+1) ≤ ρ := (mul_le_mul_of_nonneg_left cap de).trans budget
      have cur : Tube ρ z c := fun j => (disp j).trans (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (total_mono (f:=R) (fun _ => norm_nonneg _) (Nat.le_succ t)) de).trans money) (sqrt_nonneg _))
      have move (s : ℝ) (hs : s∈Set.Icc 0 1) (j : Fin m) :
          length (seg N c s-z) j≤d*total R (t+1)*length z j := by
        have mv := CircleDiscreteTracking.move_bound (N:=N) (NeZero.pos N) cur hr s hs j
        apply mv.trans ((add_le_add (disp j) (le_refl _)).trans_eq ?_)
        rw [total_succ]
        change d*total R t*length z j +d*R t*length z j = _
        ring
      have along (s : ℝ) (hs : s∈Set.Icc 0 1) : Tube ρ z (seg N c s) :=
        fun j => (move s hs j).trans (mul_le_mul_of_nonneg_right money (sqrt_nonneg _))
      obtain ⟨ge,qe⟩ := local_errors hm hρ hr energy margin angular Bcap cur along
      change ‖r (t+1)-W (r t)‖≤e*R t at ge
      have fstep : f (t+1)=W (f t) := by dsimp only [f];rw [pow_succ'];rfl
      have dg : D (t+1)≤(1-gap)*D t+e*R t := by
        have h := norm_sub_le_norm_sub_add_norm_sub (r (t+1)) (W (r t)) (f (t+1))
        rw [fstep,←map_sub] at h
        change ‖r (t+1)-f (t+1)‖ ≤ _
        rw [fstep]
        exact h.trans ((add_le_add ge (contraction hn odd (r t-f t))).trans_eq (add_comm _ _))
      refine ⟨move 1 ⟨zero_le_one,le_rfl⟩,?_,?_⟩
      · rw [total_succ,total_succ]
        linarith only [dg,bal]
      · have μstep : |y (t+1)-y t + P (K (r t))| ≤e*R t := by
          rw [population_row_factorization n hn odd 1 (by norm_num) (by norm_num)] at qe
          exact qe
        have md := (Pcap (r (t+1)-W (r t))).trans ge
        have eq : y (t+1)-P (r (t+1))-(y 0-P (r 0)) =
            (y t-P (r t)-(y 0-P (r 0)))+(y (t+1)-y t+P (K (r t)))-P (r (t+1)-W (r t)) := by
          change _ = _+_-P (r (t+1)-(r t-K (r t)))
          simp only [map_sub];ring
        rw [eq,total_succ]
        exact ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add obs μstep)) md)).trans_eq (by ring)
  obtain ⟨_,bal,obs⟩ := acc T le_rfl
  have totalCap : total R T≤2*U := by
    cases T with
    | zero => simpa [total] using (by linarith only [hU] : (0:ℝ)≤2*U)
    | succ t =>
      exact paid_next gpos hu he small (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        tri (acc t (Nat.le_succ t)).2.1 area
  have dt : D T≤e*total R T := (le_add_of_nonneg_right (mul_nonneg gpos.le (total_nn (f:=D) (fun _ => norm_nonneg _) T))).trans bal
  have ref := actual_reference (N:=N) hn z (stoppedWeight n T)
  have mode := constant_mode (N:=N) T (weight 1 n) (r 0)
  have eqrow : rowOp (fun _ : Fin N => stoppedWeight n T) (gridR N z) = P (r 0)-P (f T) := by
    change _ = P (r 0)-rowOp (fun _ => weight 1 n) (((update N)^T) (r 0))
    rw [mode]
    change rowOp (fun _ : Fin N => weight 1 n * (1-(1-gamma N)^T)) (r 0) =
      rowOp (fun _ : Fin N => weight 1 n) (r 0)-(1-gamma N)^T*rowOp (fun _ : Fin N => weight 1 n) (r 0)
    simp only [rowOp_apply,←Finset.mul_sum,mul_assoc]
    ring
  have train : trainedMean (CircleSeedIntegrability.path N m 1) T z = y T :=
    congrArg (CircleEscape.populationMean (1/sqrt (m:ℝ))) (iterate_eq_train N z T).symm
  rw [train,←ref,eqrow]
  change |y T-(y 0-(P (r 0)-P (f T)))| ≤ _
  rw [show y T-(y 0-(P (r 0)-P (f T))) =
    (y T-P (r T)-(y 0-P (r 0)))+P (r T-f T) by rw [map_sub];ring]
  exact ((abs_add_le _ _).trans (add_le_add obs ((Pcap _).trans dt))).trans
    ((by ring : 2*e*total R T+e*total R T=3*e*total R T) ▸
      (mul_le_mul_of_nonneg_left totalCap (by positivity : 0≤3*e)).trans_eq (by dsimp [e];ring))

private theorem frozen_area {N : ℕ} [NeZero N] (hn : 3≤N) (odd : Odd N) (T : ℕ)
    (v : EuclideanSpace ℝ (Fin N)) :
    (∑ t ∈ range T, ‖((update N)^t) v‖) ≤ (π*(N:ℝ))^2*‖v‖ := by
  let g := 1/(π*(N:ℝ))^2
  let f := fun t : ℕ => ((update N)^t) v
  have p : (0:ℝ)<g := by dsimp [g];positivity
  have bal (t : ℕ) : g*total (fun i => ‖f i‖) t+‖f t‖≤‖v‖ := by
    induction t with
    | zero => simp [f,total]
    | succ t ih =>
      have ds := contraction hn odd (f t)
      have h : ‖f (t+1)‖≤(1-g)*‖f t‖ := by
        dsimp only [f];rw [pow_succ'];exact ds
      rw [total_succ]
      linarith only [h,ih]
  have x := bal T
  have h : total (fun i => ‖f i‖) T≤‖v‖/g := (le_div_iff₀ p).2 (by linarith only [x,norm_nonneg (f T)])
  exact h.trans_eq (by unfold g;field_simp)

/-- Arbitrary cap, original width and Gaussian seed law. On one high-probability
event the sharp stopped error is controlled by the actual centered initialization
error and the discrete dyadic spectral budget, retaining its time truncation. -/
theorem gaussian_stopped (n k T : ℕ) (hN : 36864≤n+1) (hk : k+17≤n+1) (odd : Odd (n+1)) :
    let N := n+1
    let m := N^32
    let V := CircleTruncatedBudget.truncatedBudget odd m T
    let B := initialError N m 1
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ 14/(N:ℝ)^k ∧
      ∀ z ∈ E, |trainedMean (CircleSeedIntegrability.path N m 1) T z-
        reference N m (stoppedWeight n T) z| ≤ 6*B z*V z+44928*(1+V z)*V z/(N:ℝ)^16 := by
  intro N m V B
  obtain ⟨E,me,tail,good⟩ := CircleSharpEvent.design_event N k hN hk (by norm_num : |(1:ℝ)|≤2)
  refine ⟨E,me,tail,?_⟩
  intro z hz
  obtain ⟨_,en,rd,bsmall,marg⟩ := good z hz
  let x := (N:ℝ)
  have hd : 32≤x := by dsimp only [x];exact_mod_cast (show 32≤N by omega)
  have p : 0<x := by linarith
  have pp := pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2
  have big := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤32) hd 5
  have cmp : 4/x^7 ≤ 1/(4*(π*x)^2) := by
    rw [show x^7=x^2*x^5 by ring]
    field_simp
    nlinarith only [pp,big]
  let U := min (V z) ((π*x)^2*x^2)
  have u : 0≤U := le_min (CircleTruncatedBudget.budget_nonneg odd m T z) (by positivity)
  let ρ := randomRadius x U
  have width : sqrt (m:ℝ)=x^16 := by
    dsimp only [m,x];push_cast;rw [show ((N:ℝ)^32)=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  obtain ⟨lo,hi,budget,small⟩ := radius_budget hd u (min_le_right _ _) (bsmall.trans cmp)
  have rpos : 0≤ρ := (show 0≤1/x^16 by positivity).trans lo
  obtain ⟨gm,am⟩ := marg ρ lo hi
  have area : (∑ t ∈ range T, ‖((update N)^t) (gridR N z)‖)≤U := le_min
    (CircleDiscreteBudget.truncatedBudget_dominates odd T z)
    ((frozen_area (by omega) odd T (gridR N z)).trans (mul_le_mul_of_nonneg_left rd (sq_nonneg _)))
  have bd : 8/sqrt (m:ℝ)*(2*U)≤ρ := by
    rw [width];change 8/x^16*(2*U) ≤ randomRadius x U
    calc
      _ = 2*(8*U/x^16) := by ring
      _ ≤ _ := by linarith only [budget]
  have result := sharp_stop n m T (by omega) odd (by dsimp [m,N];positivity) z ρ (B z) U rpos hi
    (initialError_nonneg 1 z) u en gm am le_rfl small bd area
  apply result.trans
  have uv : U≤V z := min_le_left _ _
  have rbound : ρ≤32*(1+V z)/x^16 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_right uv 1) (by norm_num)) (by positivity)
  have h₁ := mul_le_mul_of_nonneg_left uv (show 0≤B z from initialError_nonneg 1 z)
  have h₂ := mul_le_mul rbound uv u (by have := CircleTruncatedBudget.budget_nonneg odd m T z; change 0≤32*(1+CircleTruncatedBudget.truncatedBudget odd m T z)/x^16; positivity)
  change 6*(B z+234*ρ)*U ≤ 6*B z*V z+44928*(1+V z)*V z/x^16
  calc
    _ = 6*(B z*U)+1404*(ρ*U) := by ring
    _ ≤ _ := (add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0:ℝ)≤6))
      (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤1404))).trans_eq (by ring)

end CircleSharpGD
