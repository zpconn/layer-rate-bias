module

public import CircleFlowTracking
public import CircleTangentDrift
public import CircleMeanDynamics
public import CircleGridSpectrum
import all CircleFlowMoments
import all CircleEscapeBridge
import all CircleSpectrum
import all CircleFlowTracking
import all CircleFlowPath
import all CircleTangentDrift
import Mathlib.Tactic

/-! The deterministic bootstrap for the actual finite-width weighted
circle-network flow, on its simultaneous initialization event. -/
public section
noncomputable section
namespace CircleActualTracking
open Real MeasureTheory Set Filter CircleFlowPath CircleTangentDrift
variable {N m : ℕ}

def gridR (N : ℕ) (z : State m) : EuclideanSpace ℝ (Fin N) :=
  rmsCoordinates (residual (circleInput N) (circleLabel N) (1/sqrt m) z)

theorem gridR_sq (z : State m) :
    ‖gridR N z‖^2 = 2*loss (residual (circleInput N) (circleLabel N) (1/sqrt m) z) := by
  rw [gridR,rmsCoordinates_norm_sq,loss]
  ring

private theorem length_entity (z : State m) (j : Fin m) :
    length z j = ‖(WithLp.toLp 2 (fun k : Fin 3 => z (j,k)) : EuclideanSpace ℝ (Fin 3))‖ := by
  apply (sq_eq_sq₀ (sqrt_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  exact sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private theorem current_length {z₀ z : State m} {ρ : ℝ} (tube : Tube ρ z₀ z) (j : Fin m) :
    length z j ≤ (1+ρ)*length z₀ j := by
  set u : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => z (j,k))
  set v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun k => z₀ (j,k))
  have diff : length (z-z₀) j = ‖u-v‖ := length_entity _ _
  have tri := norm_sub_le_norm_sub_add_norm_sub u v 0
  simp only [sub_zero] at tri
  have h := tube j
  rw [diff,length_entity z₀ j] at h
  rw [length_entity z j,length_entity z₀ j]
  change ‖u‖ ≤ (1+ρ)*‖v‖
  change ‖u-v‖ ≤ ρ*‖v‖ at h
  linarith

private theorem row_coordinate_cap {X : ℝ × ℝ} (hx : UnitInput X) (z : State m) (j : Fin m)
    (g : Fin m → ℝ) (ad : Admissible (pre z j X) (g j)) (k : Fin 3) :
    |row (1/sqrt m) z X g (j,k)| ≤ (1/sqrt m)*length z j := by
  have hL : 0 ≤ length z j := sqrt_nonneg _
  have h₁ : |X.1| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp; rw [sq_abs]
    unfold UnitInput at hx; nlinarith [sq_nonneg X.2]
  have h₂ : |X.2| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp; rw [sq_abs]
    unfold UnitInput at hx; nlinarith [sq_nonneg X.1]
  have ha : |z (j,0)*g j| ≤ length z j := by
    rw [abs_mul,abs_of_nonneg ad.1]
    exact (mul_le_mul (readout_bound _ _) ad.2.1 ad.1 hL).trans_eq (mul_one _)
  have one (v : ℝ) (hv : |v| ≤ 1) : |z (j,0)*g j*v| ≤ length z j := by
    rw [abs_mul]
    exact (mul_le_mul ha hv (abs_nonneg _) hL).trans_eq (mul_one _)
  unfold row
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/sqrt (m:ℝ))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  fin_cases k
  · change |max (pre z j X) 0| ≤ _
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (pre_bound _ _ _ hx)) hL
  · exact one X.1 h₁
  · exact one X.2 h₂

/-- The raw ODE, not a hypothesized speed bound. The squared-length definition
uses the same three coordinates as the weighted Jacobian. -/
theorem coordinate_speed {τ : ℝ} (z : State m) (g : Fin N → Fin m → ℝ) (a : Fin N → ℝ)
    (hn : 0 < N) (hτ : |τ| ≤ 2) (gates : gridGates z g) (j : Fin m) (k : Fin 3) :
    |velocity τ (fun i => row (1/sqrt m) z (circleInput N i) (g i)) a (j,k)| ≤
      2/sqrt m * ‖rmsCoordinates a‖ * length z j := by
  let H (i : Fin N) := rate τ (j,k) * row (1/sqrt m) z (circleInput N i) (g i) (j,k)
  have ratecap : |rate τ (j,k)| ≤ 2 := by unfold rate; split <;> simp_all
  have hH (i : Fin N) : |H i| ≤ 2*((1/sqrt m)*length z j) := by
    dsimp only [H]
    rw [abs_mul]
    exact mul_le_mul ratecap (row_coordinate_cap (grid_unit i) z j (g i) (gates i j) k)
      (abs_nonneg _) (by norm_num)
  have normH := rowOp_norm hn (e := 2*((1/sqrt m)*length z j)) (by
    have : 0 ≤ length z j := sqrt_nonneg _; positivity) hH
  have iden : velocity τ (fun i => row (1/sqrt m) z (circleInput N i) (g i)) a (j,k) =
      -rowOp H (rmsCoordinates a) := by
    simp only [velocity, gradient, rowOp_rms,H,Finset.sum_mul,Finset.mul_sum,div_eq_mul_inv,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros; ring
  rw [iden,abs_neg]
  exact (((rowOp H).le_opNorm _).trans (mul_le_mul_of_nonneg_right normH (norm_nonneg _))).trans_eq (by ring)

private theorem energy_ac {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    AbsolutelyContinuousOnInterval (fun s => ‖gridR N (z s)‖^2) 0 T := by
  simp_rw [gridR_sq]
  exact (loss_ac F).const_mul 2

private theorem shifted_rayleigh (A₀ A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    {k e : ℝ} (bound : ∀ v, (k+e)*‖v‖^2 ≤ inner ℝ v (A₀ v)) (close : ‖A₀-A‖ ≤ e)
    (v : EuclideanSpace ℝ (Fin N)) : k*‖v‖^2 ≤ inner ℝ v (A v) := by
  have cs := (real_inner_le_norm v ((A₀-A) v)).trans (mul_le_mul_of_nonneg_left
    (((A₀-A).le_opNorm v).trans (mul_le_mul_of_nonneg_right close (norm_nonneg v))) (norm_nonneg v))
  simp only [sub_apply,inner_sub_right] at cs
  nlinarith [bound v]

/-- On a confined prefix, the kernel comparison and the actual almost-everywhere
grid ODE imply RMS decay for the entire prefix. No measurable selection of
kink gates as a function of time is needed. -/
theorem prefix_decay {z : ℝ → State m} {τ T k ρ u : ℝ}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z)
    (G : GoodInit τ ρ u K kQ (z 0)) (hn : 0 < N) (hm : 0 < m) (hτ : |τ| ≤ 2)
    (hρ : 0 ≤ ρ) (small : ρ ≤ 1) (hu : 0 ≤ u)
    (spect : ∀ v, (k+2*(30*ρ+3*u))*‖v‖^2 ≤ inner ℝ v (gramOp K v))
    {t : ℝ} (ht : t ∈ Icc 0 T) (prefixTube : ∀ s ∈ Ico 0 t, Tube ρ (z 0) (z s)) :
    ‖gridR N (z t)‖ ≤ exp (-(k*t))*‖gridR N (z 0)‖ := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have ac : AbsolutelyContinuousOnInterval (fun s => ‖gridR N (z s)‖^2) 0 t := (energy_ac F).mono
    (by rw [uIcc_of_le ht.1,uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2)
  have bound := CircleFlowTracking.damped_comparison (k := 2*k) (M := 0) ht.1 ac (by
    filter_upwards [ae_grid_hilbert_ode F,volume.ae_ne t] with s hs hne hs'
    have hst : s ∈ Ico 0 t := ⟨hs'.1,lt_of_le_of_ne hs'.2 hne⟩
    obtain ⟨g,ad,dr⟩ := hs (by rw [uIcc_of_le hT]; exact ⟨hs'.1,hs'.2.trans ht.2⟩)
    have clos := (G.track_ops hn hm hτ hρ small hu (prefixTube s hst) ad).1
    rw [norm_sub_rev] at clos
    have damp := shifted_rayleigh _ _ spect clos (gridR N (z s))
    have energy : deriv (fun t => ‖gridR N (z t)‖^2) s =
        2 * inner ℝ (gridR N (z s)) (-(gramOp (gridGram τ (z s) g) (gridR N (z s)))) :=
      dr.norm_sq.deriv
    rw [energy,inner_neg_right]
    linarith)
  have id : exp (-(2*k*t)) = exp (-(k*t))^2 := by rw [sq,← exp_add]; congr 1; ring
  simp only [id,sub_zero,add_zero] at bound
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (exp_pos _).le (norm_nonneg _))).mp
    (by rwa [mul_pow])


private theorem tube_of_coords {ρ : ℝ} (hρ : 0 ≤ ρ) {z₀ z : State m}
    (inside : ∀ j k, |z (j,k)-z₀ (j,k)| ≤ (ρ/2)*length z₀ j) :
    Tube ρ z₀ z := by
  intro j
  have hL : 0 ≤ length z₀ j := sqrt_nonneg _
  apply (sq_le_sq₀ (show 0 ≤ length (z-z₀) j from sqrt_nonneg _) (mul_nonneg hρ hL)).mp
  rw [length_sq]
  change (z (j,0)-z₀ (j,0))^2+(z (j,1)-z₀ (j,1))^2+(z (j,2)-z₀ (j,2))^2 ≤ _
  have sqr (k : Fin 3) := pow_le_pow_left₀ (abs_nonneg _) (inside j k) 2
  have h₀ := sqr 0
  have h₁ := sqr 1
  have h₂ := sqr 2
  simp only [sq_abs] at h₀ h₁ h₂
  nlinarith [sq_nonneg (ρ*length z₀ j)]

/-- Simultaneous confinement of the actual trained neurons, and a residual
exponential at every physical time. The first candidate exit is chosen among
all three Cartesian coordinates at all neurons. -/
theorem actual_confinement {z : ℝ → State m} {τ T k ρ u R : ℝ}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z)
    (G : GoodInit τ ρ u K kQ (z 0)) (hn : 0 < N) (hm : 0 < m) (hτ : |τ| ≤ 2)
    (hT : 0 ≤ T) (hk : 0 < k) (hρ : 0 < ρ) (small : ρ ≤ 1) (hu : 0 ≤ u)
    (spect : ∀ v, (k+2*(30*ρ+3*u))*‖v‖^2 ≤ inner ℝ v (gramOp K v))
    (init : ‖gridR N (z 0)‖ ≤ R) (nonzero : ∀ j, 0 < length (z 0) j)
    (budget : 4*R/(sqrt m*k) < ρ/2) :
    ∀ t ∈ Icc 0 T, Tube ρ (z 0) (z t) ∧ ‖gridR N (z t)‖ ≤ R*exp (-(k*t)) := by
  let S (p : Coord m) := Icc 0 T ∩
    {s : ℝ | (ρ/2)*length (z 0) p.1 ≤ |z s p-z 0 p|}
  have compact (p : Coord m) : IsCompact (S p) := by
    have cont : ContinuousOn (fun s => |z s p-z 0 p|) (Icc 0 T) := by
      simpa [uIcc_of_le hT] using ((F.ac p).continuousOn.sub continuousOn_const).abs
    exact isCompact_Icc.of_isClosed_subset
      (cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  have noexit : ¬ (⋃ p, S p).Nonempty := by
    intro ne
    obtain ⟨t, ht, first⟩ := (isCompact_iUnion compact).exists_isMinOn ne continuous_id.continuousOn
    obtain ⟨p,hp⟩ := mem_iUnion.mp ht
    have htime : t ∈ Icc 0 T := hp.1
    have allprev (s : ℝ) (hs : s ∈ Ico 0 t) : Tube ρ (z 0) (z s) := by
      apply tube_of_coords hρ.le
      intro j l
      by_contra! bad
      exact hs.2.not_ge (isMinOn_iff.mp first s (mem_iUnion.mpr
        ⟨(j,l), ⟨hs.1,hs.2.le.trans htime.2⟩,bad.le⟩))
    have decay (s : ℝ) (hs : s ∈ Ico 0 t) : ‖gridR N (z s)‖ ≤ R*exp (-(k*s)) := by
      have h := prefix_decay F G hn hm hτ hρ.le small hu spect
        (show s ∈ Icc 0 T from ⟨hs.1,hs.2.le.trans htime.2⟩)
        (fun y hy => allprev y ⟨hy.1, hy.2.trans hs.2⟩)
      exact h.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left init (exp_pos _).le)
    have acp : AbsolutelyContinuousOnInterval (fun s => z s p) 0 t := (F.ac p).mono
      (by rw [uIcc_of_le hT,uIcc_of_le htime.1]; exact Icc_subset_Icc_right htime.2)
    have hR := (norm_nonneg _).trans init
    have hlen := (nonzero p.1).le
    have d := CircleFlowTracking.integrated_velocity (k := k) (C := (4*R/sqrt m)*length (z 0) p.1)
      htime.1 hk (by positivity) acp (by
        filter_upwards [F.compatible,volume.ae_ne t] with s hs neq hst
        have st : s ∈ Ico 0 t := ⟨hst.1,lt_of_le_of_ne hst.2 neq⟩
        obtain ⟨g,ad,dz⟩ := hs (by rw [uIcc_of_le hT]; exact ⟨hst.1,hst.2.trans htime.2⟩)
        rw [(dz p).deriv]
        have v := coordinate_speed (z s) g (residual (circleInput N) (circleLabel N) (1/sqrt m) (z s))
          hn hτ ad p.1 p.2
        have size := (current_length (allprev s st) p.1).trans
          (mul_le_mul_of_nonneg_right (by linarith : 1+ρ ≤ 2) hlen)
        have fac : 0 ≤ 2/sqrt (m:ℝ) := by positivity
        apply v.trans
        change 2/sqrt m * ‖gridR N (z s)‖ * length (z s) p.1 ≤ _
        calc
          _ ≤ 2/sqrt m * (R*exp (-(k*s))) * (2*length (z 0) p.1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (decay s st) fac) size
              (by exact sqrt_nonneg _) (by positivity)
          _ = _ := by ring)
    have excl : (4*R/sqrt m)*length (z 0) p.1/k < (ρ/2)*length (z 0) p.1 := by
      convert mul_lt_mul_of_pos_right budget (nonzero p.1) using 1
      ring
    exact (d.trans_lt excl).not_ge hp.2
  have alltube (s : ℝ) (hs : s ∈ Icc 0 T) : Tube ρ (z 0) (z s) := by
    apply tube_of_coords hρ.le
    intro j l
    by_contra! bad
    exact noexit ⟨s,mem_iUnion.mpr ⟨(j,l),hs,bad.le⟩⟩
  intro t ht
  refine ⟨alltube t ht,?_⟩
  have h := prefix_decay F G hn hm hτ hρ.le small hu spect ht
    (fun s hs => alltube s ⟨hs.1,hs.2.le.trans ht.2⟩)
  exact h.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left init (exp_pos _).le)


private theorem row_ac {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) (a : Fin N → ℝ) :
    AbsolutelyContinuousOnInterval (fun s => rowOp a (gridR N (z s))) 0 T := by
  let r (s : ℝ) := residual (circleInput N) (circleLabel N) (1/sqrt m) (z s)
  have sum := CircleFlowPath.acsum Finset.univ (fun i s => a i*r s i)
    (fun i _ => (residual_ac F i).const_mul (a i))
  have h := sum.const_mul (N:ℝ)⁻¹
  simp_rw [gridR,rowOp_rms]
  convert h using 1
  ext s
  change (∑ i, a i*r s i)/N = (N:ℝ)⁻¹*∑ i, a i*r s i
  ring

/-- Output tracking from the changing angular row and the *same* grid
Jacobian along a realized path. The estimates use no temporal independence
or separately selected grid and test gates. -/
theorem actual_endpoint {z : ℝ → State m} {τ T k ρ u R b : ℝ}
    {K : Matrix (Fin N) (Fin N) ℝ} {kQ : Fin N → ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z)
    (G : GoodInit τ ρ u K kQ (z 0)) (hn : 0 < N) (hm : 0 < m) (hτ : |τ| ≤ 2)
    (hT : 0 ≤ T) (hk : 0 < k) (hρ : 0 < ρ) (small : ρ ≤ 1) (hu : 0 ≤ u)
    (spect : ∀ v, (k+2*(30*ρ+3*u))*‖v‖^2 ≤ inner ℝ v (gramOp K v))
    (init : ‖gridR N (z 0)‖ ≤ R) (nonzero : ∀ j, 0 < length (z 0) j)
    (budget : 4*R/(sqrt m*k) < ρ/2) (hb : |b| ≤ 1)
    (eig : rowOp kQ = (rowOp (fun _ : Fin N => b)).comp (gramOp K)) :
    ‖gridR N (z T)‖ ≤ R*exp (-(k*T)) ∧
    |CircleFlowMoments.mean (z T)-(CircleFlowMoments.mean (z 0)-rowOp (fun _ => b) (gridR N (z 0)))| ≤
      2*(2*(30*ρ+3*u))*R/k + R*exp (-(k*T)) := by
  let p := rowOp (fun _ : Fin N => b)
  let e := 2*(30*ρ+3*u)
  have hR := (norm_nonneg _).trans init
  have epos : 0 ≤ e := by dsimp [e]; positivity
  have pcap : ‖p‖ ≤ 1 := rowOp_norm hn zero_le_one (fun _ => hb)
  have conf := actual_confinement F G hn hm hτ hT hk hρ small hu spect init nonzero budget
  obtain ⟨_,fit⟩ := conf T ⟨hT,le_rfl⟩
  refine ⟨fit,?_⟩
  have ac := (CircleMeanDynamics.mean_ac F).fun_sub (row_ac F (fun _ => b))
  have tel := CircleFlowTracking.integrated_velocity (k := k) (C := 2*e*R) hT hk (by positivity) ac (by
    filter_upwards [CircleMeanDynamics.ae_joint_ode hm F] with s hs hmem
    obtain ⟨g,ad,dr,dy⟩ := hs (by simpa [uIcc_of_le hT] using hmem)
    obtain ⟨tube,dec⟩ := conf s hmem
    obtain ⟨gr,mn⟩ := G.track_ops hn hm hτ hρ.le small hu tube ad
    let A := gramOp (gridGram τ (z s) g)
    let q := rowOp (populationRow τ (z s) g)
    have projected := (p.opNorm_comp_le (gramOp K-A)).trans (mul_le_mul pcap
      (by simpa [A,norm_sub_rev] using gr : ‖gramOp K-A‖ ≤ e) (norm_nonneg _) zero_le_one)
    rw [ContinuousLinearMap.comp_sub,one_mul] at projected
    have rowerr : ‖q-p.comp A‖ ≤ 2*e := by
      rw [eig] at mn
      exact (norm_sub_le_norm_sub_add_norm_sub _ (p.comp (gramOp K)) _).trans
        ((add_le_add mn projected).trans_eq (by ring))
    have d := dy.sub (p.hasFDerivAt.comp_hasDerivAt s dr)
    rw [show deriv (fun t => CircleFlowMoments.mean (z t)-p (gridR N (z t))) s = _ from d.deriv]
    change |-(q (gridR N (z s)))-p (-(A (gridR N (z s))))| ≤ _
    rw [map_neg,sub_neg_eq_add,show -(q (gridR N (z s)))+p (A (gridR N (z s))) =
      -((q-p.comp A) (gridR N (z s))) by simp; ring]
    rw [abs_neg]
    exact (((q-p.comp A).le_opNorm _).trans
      (mul_le_mul rowerr dec (norm_nonneg _) (by positivity))).trans_eq (by ring))
  have hp := (p.le_opNorm (gridR N (z T))).trans
    (mul_le_mul pcap fit (norm_nonneg _) zero_le_one)
  rw [one_mul,Real.norm_eq_abs] at hp
  let Y (t : ℝ) := CircleFlowMoments.mean (z t)
  let r (t : ℝ) := gridR N (z t)
  change |Y T-(Y 0-p (r 0))| ≤ _
  rw [show Y T-(Y 0-p (r 0)) = ((Y T-p (r T))-(Y 0-p (r 0)))+p (r T) by ring]
  exact (abs_add_le _ _).trans (add_le_add tel hp)



/-- The polynomial schedule for the deterministic high-probability proof. -/
def designRadius (N : ℝ) := 32*π^2/N^12
def designTolerance (N : ℝ) := 1/N^7
def designDecay (N : ℝ) := 3/(4*π^2*N^2)

theorem design_bounds {N : ℝ} (hN : 32 ≤ N) :
    designRadius N ≤ 1 ∧ 2*(30*designRadius N+3*designTolerance N) ≤ 66/N^7 ∧
    designDecay N+2*(30*designRadius N+3*designTolerance N) ≤ 1/(π*N)^2 ∧
    4*N^2/(N^16*designDecay N) < designRadius N/2 := by
  have hn : 0 < N := by linarith
  have pp : π^2 ≤ 16 := by
    have h := pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2
    norm_num at h
    exact h
  have n5 : (32:ℝ)^5 ≤ N^5 := pow_le_pow_left₀ (by norm_num) hN 5
  have n7 : (1:ℝ) ≤ N^7 := one_le_pow₀ (by linarith : 1 ≤ N)
  have rho : designRadius N ≤ 1/N^7 := by
    unfold designRadius
    rw [show N^12=N^7*N^5 by ring]
    have hn5 : (0:ℝ) < N^5 := by positivity
    field_simp
    nlinarith
  have ee : 2*(30*designRadius N+3*designTolerance N) ≤ 66/N^7 := by
    dsimp [designTolerance]
    simp only [div_eq_mul_inv,one_mul] at rho ⊢
    linarith
  refine ⟨rho.trans ((div_le_one (by positivity)).mpr n7),ee,?_,?_⟩
  · apply (add_le_add_right ee _).trans
    unfold designDecay
    have haux : 66/N^7 ≤ 1/(4*π^2*N^2) := by
      rw [show N^7=N^2*N^5 by ring]
      field_simp
      nlinarith
    apply (add_le_add_right haux _).trans_eq
    field_simp
    ring
  · unfold designRadius designDecay
    field_simp
    nlinarith [mul_pos (sq_pos_of_pos pi_pos) (pow_pos hn 14)]

/-- A three-quarter population gap fits even the larger radius R=N² by
the original physical time. The rounded-up time can only improve decay. -/
theorem design_time {N : ℝ} (hN : 1 ≤ N) :
    N^2*exp (-(designDecay N*(CircleFlowTracking.horizon N))) ≤ 1/N^3 := by
  have hn : 0 < N := by linarith
  have hh := Nat.le_ceil (2*π^2*N^2*log (2*sqrt (12*N)*N^3))
  change 2*π^2*N^2*log (2*sqrt (12*N)*N^3) ≤ (CircleFlowTracking.horizon N : ℝ) at hh
  have logs : (5:ℝ)*log N ≤ (3/2)*log (2*sqrt (12*N)*N^3) := by
    rw [log_mul (by positivity) (by positivity),log_mul (by norm_num) (by positivity),
      log_sqrt (by positivity),log_mul (by norm_num) hn.ne',log_pow]
    norm_num
    linarith [log_nonneg hN, log_nonneg (by norm_num : (1:ℝ) ≤ 2),log_nonneg (by norm_num : (1:ℝ) ≤ 12)]
  have rate : 5*log N ≤ designDecay N * (CircleFlowTracking.horizon N : ℝ) :=
    logs.trans ((show (3/2)*log (2*sqrt (12*N)*N^3) =
      designDecay N*(2*π^2*N^2*log (2*sqrt (12*N)*N^3)) by unfold designDecay; field_simp; ring).le.trans
      (mul_le_mul_of_nonneg_left hh (by unfold designDecay; positivity)))
  have ee := exp_le_exp.mpr (neg_le_neg rate)
  rw [show exp (-(5*log N)) = (N^5)⁻¹ by
    rw [show 5*log N=log (N^5) by rw [log_pow]; norm_num,exp_neg,exp_log (by positivity)]] at ee
  exact (mul_le_mul_of_nonneg_left ee (sq_nonneg N)).trans_eq (by field_simp)

/-- The telescope reference coincides with the fixed grid-interpolation
statistic of the original network. This includes the exact teacher mean. -/
theorem actual_reference (hN : 3 ≤ N) (z : State m) (b : ℝ) :
    CircleFlowMoments.mean z - rowOp (fun _ : Fin N => b) (gridR N z) =
      CircleEscapeBridge.reference N m b z := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have zero := CircleGridMoments.projection_sum N hN 1
  simp [Complex.inner] at zero
  change (∑ i, (CircleEscape.gridPoint N i).re) = 0 at zero
  have labels : (∑ i, circleLabel N i) = N := by
    simp [circleLabel,circleInput,Finset.sum_add_distrib,zero]
  rw [gridR,rowOp_rms]
  change CircleFlowMoments.mean z - _ = CircleFlowMoments.mean z -
    b*((∑ i, CircleEscape.output (1/sqrt m) (CircleEscapeBridge.initial z) (CircleEscape.gridPoint N i))/N-1)
  simp only [← Finset.mul_sum,CircleFlowPath.residual,Finset.sum_sub_distrib,labels,CircleFlowMoments.output_eq_complex]
  field_simp


/-- Interpolation weights from the actual positive spectrum obey the row cap. -/
theorem weight_abs_le_one (n : ℕ) (τ : ℝ) (ht : 0 ≤ τ) : |CircleSpectrum.weight τ n| ≤ 1 := by
  have hU : 0 ≤ CircleSpectrum.U τ n := by
    unfold CircleSpectrum.U CircleSpectrum.scaledU
    apply mul_nonneg (by unfold CircleSpectrum.rp; positivity)
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro j
    have hh := (CircleSpectrum.offset_bounds n j).1
    unfold CircleSpectrum.rp
    positivity
  have h0 : 0 < CircleSpectrum.k0 τ := by unfold CircleSpectrum.k0; positivity
  have hden := add_pos_of_pos_of_nonneg h0 hU
  unfold CircleSpectrum.weight
  rw [abs_of_nonneg (div_nonneg h0.le hden.le),div_le_one hden]
  linarith

/-- Explicit deterministic endpoint for the full specified network, two
trainable layers, actual circle labels and original physical horizon.
Only initial configuration events enter, with no dynamical hypotheses beyond
the definition of the trajectory and its nonzero initial neuron lengths. -/
theorem design_endpoint (n : ℕ) (hN : 32 ≤ n+1) (ho : Odd (n+1))
    (τ : ℝ) (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2)
    (z : ℝ → State ((n+1)^32))
    (F : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
      (CircleFlowTracking.horizon (n+1)) z)
    (G : GoodInit τ (designRadius (n+1)) (designTolerance (n+1))
      (CircleGridSpectrum.sampledMatrix τ) (fun _ : Fin (n+1) => CircleSpectrum.k0 τ) (z 0))
    (init : ‖gridR (n+1) (z 0)‖ ≤ ((n:ℝ)+1)^2)
    (nz : ∀ j, 0 < length (z 0) j) :
    ‖gridR (n+1) (z (CircleFlowTracking.horizon (n+1)))‖ ≤ 1/((n:ℝ)+1)^3 ∧
    |CircleFlowMoments.mean (z (CircleFlowTracking.horizon (n+1))) -
      CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) (z 0)| ≤
        (1+176*π^2)/((n:ℝ)+1)^3 := by
  let D := (n:ℝ)+1
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast hN
  have Dpos : 0 < D := by linarith
  have h3 : 3 ≤ n+1 := by omega
  have htτ : |τ| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; exact hτ'
  have radpos : 0 < designRadius D := by dsimp [designRadius]; positivity
  have upos : 0 ≤ designTolerance D := by dsimp [designTolerance]; positivity
  have kpos : 0 < designDecay D := by dsimp [designDecay]; positivity
  obtain ⟨rs,ecap,sc,budget⟩ := design_bounds d
  have width : sqrt (((n+1)^32 : ℕ):ℝ)=D^16 := by
    push_cast
    rw [show ((n:ℝ)+1)^32=(((n:ℝ)+1)^16)^2 by ring, sqrt_sq (by positivity)]
  have spec (v : EuclideanSpace ℝ (Fin (n+1))) :=
    CircleGridSpectrum.gramOp_gap h3 ho τ hτ hτ' v
  have castN : ((n+1 : ℕ):ℝ) = D := by simp [D]
  simp only [castN] at spec
  have bd : 4*D^2/(sqrt (((n+1)^32 : ℕ):ℝ)*designDecay D) < designRadius D/2 := by rw [width]; exact budget
  have result := actual_endpoint (N := n+1) (m := (n+1)^32) (k := designDecay D) (R := D^2) F G (Nat.succ_pos _)
    (pow_pos (Nat.succ_pos _) _) htτ (by positivity) kpos radpos rs upos
    (fun v => (mul_le_mul_of_nonneg_right sc (sq_nonneg _)).trans (spec v))
    init nz bd (weight_abs_le_one n τ (by linarith))
    (CircleGridSpectrum.population_row_factorization n h3 ho τ hτ hτ')
  have delay := design_time (show 1 ≤ D by linarith)
  rw [actual_reference h3] at result
  refine ⟨result.1.trans delay,result.2.trans ?_⟩
  calc
    _ ≤ 2*(66/D^7)*D^2/designDecay D + 1/D^3 :=
      add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ecap (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg _)) kpos.le) delay
    _ = _ := by change _ = (1+176*π^2)/D^3; unfold designDecay; field_simp; ring

end CircleActualTracking
