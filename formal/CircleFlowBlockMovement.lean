module

public import CircleActiveSpeed
public import CircleActualTracking
import all CircleActualTracking
import all CircleFlowTracking
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Tactic

/-! Per-neuron displacement for a compatible equal-rate circle flow. -/
@[expose] public section
noncomputable section
namespace CircleFlowBlockMovement
open Real MeasureTheory Set CircleActualTracking CircleFlowPath CircleTangentDrift
variable {N m : ℕ} {T : ℝ} {z : ℝ → State m}

private def projection (a : Fin 3 → ℝ) (v : State m) (j : Fin m) := ∑ k, a k*v (j,k)
private abbrev block (v : State m) (j : Fin m) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun k => v (j,k))

private theorem projection_bound (v w : State m) (j : Fin m) :
    projection (fun k => v (j,k)) w j ≤ length v j * length w j := by
  rw [length_entity,length_entity]
  have h := real_inner_le_norm (block v j) (block w j)
  simpa only [PiLp.inner_apply,Real.inner_apply,projection,block,WithLp.ofLp_toLp,PiLp.toLp_apply,
    mul_comm] using h

private theorem proj_self (v : State m) (j : Fin m) :
    projection (fun k => v (j,k)) v j = length v j^2 := by
  unfold projection;unfold length;rw [sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [sq]

private abbrev flow (N : ℕ) (T : ℝ) (z : ℝ → State m) :=
  IsFlow (circleInput N) (circleLabel N) (1/sqrt m) 1 T z

private abbrev vel (v : State m) (g : Fin N → Fin m → ℝ) :=
  velocity 1 (fun i => row (1/sqrt m) v (circleInput N i) (g i)) (residual (circleInput N) (circleLabel N) (1/sqrt m) v)

private theorem len_cont (F : flow N T z) (j : Fin m) :
    ContinuousOn (fun t => length (z t) j) (uIcc 0 T) := by
  unfold length;apply ContinuousOn.sqrt;exact continuousOn_finsetSum _ (fun k _ => (F.ac (j,k)).continuousOn.pow 2)

private theorem norm_grid_cont (F : flow N T z) :
    ContinuousOn (fun t => ‖gridR N (z t)‖) (uIcc 0 T) := by
  simpa only [sqrt_sq (norm_nonneg _)] using (energy_ac F).continuousOn.sqrt

private theorem motion_core (ht : 0≤T) (F : flow N T z) (j : Fin m)
    (speed : ∀ t, t∈uIcc 0 T → ∀ (g : Fin N → Fin m → ℝ), gridGates (z t) g →
      length (vel (z t) g) j≤(‖gridR N (z t)‖/√m)*length (z t) j) :
    length (z T-z 0) j ≤ ∫ s in (0:ℝ)..T, (‖gridR N (z s)‖/√m)*length (z s) j := by
  let d := z T-z 0
  let L := length d j
  let h s := (‖gridR N (z s)‖/√m)*length (z s) j
  let Y s := projection (fun k => d (j,k)) (z s) j
  have hl : 0≤L := sqrt_nonneg _
  have hi : IntervalIntegrable h volume 0 T :=
    (((norm_grid_cont F).div_const _).mul (len_cont F j)).intervalIntegrable
  by_cases pos : 0<L
  · have ac : AbsolutelyContinuousOnInterval Y 0 T := acsum _ _ (fun k _ => (F.ac (j,k)).const_mul (d (j,k)))
    have derivs : ∀ᵐ s : ℝ, s∈Icc 0 T → deriv Y s ≤ L*h s := by
      filter_upwards [F.compatible] with s hs
      intro t
      have mem : s∈uIcc 0 T := (uIcc_of_le ht).symm ▸ t
      obtain ⟨g,hg,hv⟩ := hs mem
      have der : HasDerivAt Y (projection (fun k => d (j,k)) (vel (z s) g) j) s :=
        HasDerivAt.fun_sum (u:=Finset.univ) (fun k _ => (hv (j,k)).const_mul (d (j,k)))
      rw [der.deriv]
      exact (projection_bound d _ j).trans (mul_le_mul_of_nonneg_left (speed s mem g hg) hl)
    have hmon := intervalIntegral.integral_mono_ae_restrict ht ac.intervalIntegrable_deriv
      (hi.const_mul L) ((ae_restrict_iff' measurableSet_Icc).mpr derivs)
    rw [ac.integral_deriv_eq_sub,intervalIntegral.integral_const_mul] at hmon
    have id : Y T-Y 0=L*L := by
      change (∑ k,d (j,k)*z T (j,k))-(∑ k,d (j,k)*z 0 (j,k))=_
      rw [←Finset.sum_sub_distrib,←sq,←show length d j=L from rfl,←proj_self]
      apply Finset.sum_congr rfl;intro k _;dsimp [d];ring
    exact (le_of_mul_le_mul_left (id ▸ hmon) pos)
  · have eq := le_antisymm (le_of_not_gt pos) hl
    change L≤_;rw [eq]
    exact intervalIntegral.integral_nonneg ht fun s _ => mul_nonneg (by positivity) (sqrt_nonneg _)

private theorem zero_core (ht : 0≤T) (F : flow N T z) (j : Fin m) (zero : length (z 0) j=0)
    (speed : ∀ t, t∈uIcc 0 T → ∀ (g : Fin N → Fin m → ℝ), gridGates (z t) g →
      length (vel (z t) g) j≤(‖gridR N (z t)‖/√m)*length (z t) j) :
    length (z T) j=0 := by
  let E s := length (z s) j^2
  let K s := ‖gridR N (z s)‖/√m
  have id (s : ℝ) : E s = ∑ k : Fin 3, (z s (j,k))^2 := sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have ac : AbsolutelyContinuousOnInterval E 0 T := by
    rw [funext id]
    exact acsum _ _ (fun k _ => by simpa only [sq] using (F.ac (j,k)).fun_mul (F.ac (j,k)))
  obtain ⟨p,_,hK⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc ((norm_grid_cont F).div_const (√m))
  have t0 := CircleFlowTracking.zero_unit_fixed (d:=E) (c:=2*K p) ht ac
    (show E 0=0 by dsimp [E];rw [zero];norm_num) (sq_nonneg _) (by
      filter_upwards [F.compatible] with s hs
      intro t
      have mem : s∈uIcc 0 T := (uIcc_of_le ht).symm ▸ t
      obtain ⟨g,hg,hv⟩ := hs mem
      let v := vel (z s) g
      have der : HasDerivAt E (∑ k : Fin 3, 2*(z s (j,k))*v (j,k)) s := by
        rw [funext id];exact HasDerivAt.fun_sum (u:=Finset.univ) (fun k _ => by simpa [v,vel] using! (hv (j,k)).fun_pow 2)
      rw [der.deriv]
      have proj := projection_bound (z s) v j
      have b := mul_le_mul_of_nonneg_left (speed s mem g hg) (sqrt_nonneg (∑ k : Fin 3,(z s (j,k))^2))
      have a : K s≤K p := hK mem
      have H := mul_le_mul_of_nonneg_right a (sq_nonneg (length (z s) j))
      change length (z s) j*length v j≤length (z s) j*(K s*length (z s) j) at b
      simp_rw [mul_assoc (2:ℝ),←Finset.mul_sum]
      change 2*projection (fun k => z s (j,k)) v j≤2*(K p * (length (z s) j)^2)
      nlinarith only [proj,b,H])
  exact sq_eq_zero_iff.mp t0


/-- The integral of the full three-coordinate neuron speed controls its displacement. -/
theorem movement (hn : 0<N) (ht : 0≤T)
    (F : IsFlow (circleInput N) (circleLabel N) (1/√m) 1 T z) (j : Fin m) :
    length (z T-z 0) j ≤ ∫ s in (0:ℝ)..T, (‖gridR N (z s)‖/√m)*length (z s) j :=
  motion_core ht F j fun t _ g hg => CircleActiveSpeed.velocity_le hn (z t) g hg j

/-- An initially zero three-coordinate neuron remains zero. -/
theorem zero_fixed (hn : 0<N) (ht : 0≤T)
    (F : IsFlow (circleInput N) (circleLabel N) (1/√m) 1 T z) (j : Fin m) (zero : length (z 0) j=0) :
    length (z T) j=0 := zero_core ht F j zero fun t _ g hg => CircleActiveSpeed.velocity_le hn (z t) g hg j

private theorem restrict_flow (F : flow N T z) {t : ℝ} (ht : t∈Icc 0 T) : flow N t z := by
  have sub : uIcc 0 t⊆uIcc 0 T := by
    rw [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)];exact Icc_subset_Icc_right ht.2
  exact ⟨fun p => (F.ac p).mono sub,F.compatible.mono (fun _ h _ht => h (sub _ht))⟩

theorem movement_prefix (hn : 0<N) (F : IsFlow (circleInput N) (circleLabel N) (1/√m) 1 T z)
    {t : ℝ} (ht : t∈Icc 0 T) (j : Fin m) :
    length (z t-z 0) j ≤ ∫ s in (0:ℝ)..t, (‖gridR N (z s)‖/√m)*length (z s) j :=
  movement hn ht.1 (restrict_flow F ht) j

theorem zero_fixed_prefix (hn : 0<N) (F : IsFlow (circleInput N) (circleLabel N) (1/√m) 1 T z)
    {t : ℝ} (ht : t∈Icc 0 T) (j : Fin m) (init : length (z 0) j=0) :
    length (z t-z 0) j=0 := by
  have final := zero_fixed hn ht.1 (restrict_flow F ht) j init
  rw [length_entity] at final init ⊢
  change ‖block (z t) j-block (z 0) j‖=0
  rw [show block (z t) j=0 from norm_eq_zero.mp final,show block (z 0) j=0 from norm_eq_zero.mp init];simp

end CircleFlowBlockMovement
