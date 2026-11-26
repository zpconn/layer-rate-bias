module

public import CircleInclusionExistence
public import CirclePathSelection
import Mathlib.Analysis.Calculus.Deriv.Prod
public import CircleFlowTracking
import all CircleFlowPath
import Mathlib.Tactic

/-! Localizing the actual circle chamber field on physical-time horizons. -/
@[expose] public section
noncomputable section
namespace CircleLocalContinuation
open CircleFlowPath CirclePathSelection MeasureTheory Set Metric
open scoped NNReal

abbrev Field (N m : ℕ) (τ : ℝ) : State m → Set (State m) :=
  chamberField (circleInput N) (circleLabel N) (1/Real.sqrt m) τ

/-- Coordinate clipping to a closed sup-norm ball. -/
def clip {m : ℕ} (R : ℝ≥0) (z : State m) : State m :=
  fun i => max (-(R:ℝ)) (min (R:ℝ) (z i))

theorem clip_continuous (m : ℕ) (R : ℝ≥0) : Continuous (clip (m:=m) R) := by
  unfold clip
  fun_prop

theorem norm_clip {m : ℕ} (R : ℝ≥0) (z : State m) : ‖clip R z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg R.2).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [R.2]) (min_le_left _ _)⟩

theorem clip_eq_self {m : ℕ} (R : ℝ≥0) {z : State m} (hz : ‖z‖ ≤ R) : clip R z = z := by
  funext i
  have h := (pi_norm_le_iff_of_nonneg R.2).mp hz i
  rw [Real.norm_eq_abs,abs_le] at h
  change max (-(R:ℝ)) (min (R:ℝ) (z i)) = z i
  exact le_antisymm (max_le h.1 (min_le_right _ _))
    ((le_min h.2 le_rfl).trans (le_max_right _ _))

/-- Convert an a.e. actual chamber velocity to the compatible weighted path
hypotheses, preserving the specific path and all simultaneous kinks. -/
theorem flow_of_derivatives {N m : ℕ} {τ T : ℝ} {z : ℝ → State m} (hT : 0 ≤ T)
    (ac : ∀ k, AbsolutelyContinuousOnInterval (fun t => z t k) 0 T)
    (incl : ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ Field N m τ (z t), HasDerivAt z v t) :
    IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T z := by
  apply isFlow_of_incident ac
  rw [uIcc_of_le hT]
  filter_upwards [incl] with t ht hmem
  obtain ⟨v,hv,hd⟩ := ht hmem
  have e : curveVelocity z t = v := funext (fun k => (hasDerivAt_pi.mp hd k).deriv)
  rw [e]
  exact chamberField_subset_incident _ _ _ _ _ hv

private theorem norm_le_of_kinetic {m : ℕ} (z : State m) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2) :
    ‖z‖ ≤ Real.sqrt (2*kinetic τ z) := by
  have rp (i : Coord m) : 0 < rate τ i ∧ rate τ i ≤ 2 := by
    unfold rate; split <;> constructor <;> first | assumption | norm_num
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have term (k : Coord m) : 0 ≤ (z k)^2/rate τ k := div_nonneg (sq_nonneg _) (rp k).1.le
  have pos : 0 ≤ kinetic τ z := Finset.sum_nonneg fun i _ => term i
  have sum : (z i)^2/rate τ i ≤ kinetic τ z :=
    Finset.single_le_sum (fun k _ => term k) (Finset.mem_univ i)
  rw [Real.le_sqrt (abs_nonneg _) (by positivity),sq_abs]
  apply le_trans ((div_le_iff₀ (rp i).1).mp sum)
  have cmp := mul_le_mul_of_nonneg_left (rp i).2 pos
  linarith

/-- A single radius strictly confines all true prefixes from the seed ball,
simultaneously for all times through T. -/
theorem radius_on_horizon (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2)
    (a T : ℝ≥0) :
    ∃ R : ℝ≥0, a < R ∧ ∀ (z : ℝ → State m), ‖z 0‖ ≤ a →
      ∀ t ∈ Icc 0 (T:ℝ), IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ t z → ‖z t‖ < R := by
  have kc : Continuous (kinetic (m:=m) τ) := by unfold kinetic; fun_prop
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0 : State m) a).bddAbove_image kc.continuousOn
  let M := max (a:ℝ) (Real.sqrt (2*K+3*T))
  let R : ℝ≥0 := ⟨M+1,by dsimp [M]; positivity⟩
  have aM : (a:ℝ) ≤ M := le_max_left _ _
  have kM : Real.sqrt (2*K+3*T) ≤ M := le_max_right _ _
  refine ⟨R,show (a:ℝ)<M+1 by linarith,?_⟩
  intro z hx t ht hz
  have init : kinetic τ (z 0) ≤ K := hK (mem_image_of_mem _ (by simpa [mem_closedBall,dist_zero_right] using hx))
  have rad := (circle_path_bounds hN hτ h2 ht.1 hz).1
  have sq : 2*kinetic τ (z t) ≤ 2*K+3*T := by linarith [ht.2]
  have lim := (norm_le_of_kinetic (z t) hτ h2).trans ((Real.sqrt_le_sqrt sq).trans kM)
  change ‖z t‖ < M+1
  linarith

/-- Uniform actual velocity bounds on compact state balls, obtained from the
compact chamber graph. -/
theorem velocity_on_ball (N m : ℕ) (τ : ℝ) (R : ℝ≥0) :
    ∃ L : ℝ≥0, ∀ z : State m, ‖z‖ ≤ R → ∀ v ∈ Field N m τ z, ‖v‖ ≤ L := by
  have graph := (circle_chamber_regularity N m (1/Real.sqrt m) τ).2.2.1 _
    (isCompact_closedBall (0 : State m) R)
  obtain ⟨K,hK⟩ := graph.bddAbove_image (f := fun q => ‖q.2‖) continuous_snd.norm.continuousOn
  refine ⟨⟨max K 0,le_max_right _ _⟩,?_⟩
  intro z hz v hv
  apply (le_trans _ (le_max_left _ _))
  exact hK ⟨(z,v), ⟨hv,by simpa [mem_closedBall,dist_zero_right] using hz⟩,rfl⟩

theorem velocity_bound_on_horizon (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2)
    (a T : ℝ≥0) :
    ∃ L : ℝ≥0, ∀ (z : ℝ → State m), ‖z 0‖ ≤ a → ∀ t ∈ Icc 0 (T:ℝ),
      IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ t z →
      ∀ v ∈ Field N m τ (z t), ‖v‖ ≤ L := by
  obtain ⟨R,_,rad⟩ := radius_on_horizon N m hN hτ h2 a T
  obtain ⟨L,speed⟩ := velocity_on_ball N m τ R
  exact ⟨L, fun z hz t ht hf => speed _ (rad z hz t ht hf).le⟩


open CircleInclusionExistence

/-- The unmodified chamber inclusion has a trajectory through every prescribed
physical horizon from every seed. The clipped global solution is used only to
construct a witness, and confinement removes the clipping up to T. -/
theorem exists_on_horizon (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2)
    (x : State m) (T : ℝ≥0) :
    ∃ p : C(ℝ≥0,State m), p 0 = x ∧ (∃ L : ℝ≥0, LipschitzWith L p) ∧
      ∀ᵐ t : ℝ, t ∈ Icc 0 (T:ℝ) → ∃ v ∈ Field N m τ (realPath p t), HasDerivAt (realPath p) v t := by
  obtain ⟨R,_,rad⟩ := radius_on_horizon N m hN hτ h2 ‖x‖₊ T
  obtain ⟨L,bound⟩ := velocity_on_ball N m τ R
  let F := Field N m τ
  let G := F ∘ clip R
  have reg := circle_chamber_regularity N m (1/Real.sqrt m) τ
  have uh : UpperHemicontinuous G := by
    apply upperHemicontinuous_iff_isOpen_preimage_Iic.mpr
    intro U hU
    exact ((upperHemicontinuous_iff_isOpen_preimage_Iic.mp reg.2.1) U hU).preimage (clip_continuous m R)
  obtain ⟨p,hinit,lip,inc⟩ := exists_solution_bounded_field G uh (fun z => (reg.1 (clip R z)).1)
    (fun z => (reg.1 (clip R z)).2.2) (fun z => (reg.1 (clip R z)).2.1.isClosed) L
    (fun z => bound _ (norm_clip R z)) x
  let z := realPath p
  have rlip : LipschitzWith L z := by
    change LipschitzWith L (p ∘ Real.toNNReal)
    simpa only [mul_one] using lip.comp Real.lipschitzWith_toNNReal
  have coord (k : Coord m) : LipschitzWith L (fun t => z t k) :=
    LipschitzWith.of_dist_le_mul (fun s t => (dist_le_pi_dist _ _ k).trans (rlip.dist_le_mul s t))
  have zinit : z 0 = x := by simpa [z,realPath] using hinit
  have confined : ∀ t ∈ Icc 0 (T:ℝ), ‖z t‖ < R := by
    apply CircleFlowTracking.no_first_exit z.continuous.norm.continuousOn
    intro t ht prev
    apply rad z (by simp [zinit]) t ht
    apply flow_of_derivatives ht.1 (fun k => (coord k).lipschitzOnWith.absolutelyContinuousOnInterval)
    filter_upwards [inc t,volume.ae_ne t] with s h hsne hs
    obtain ⟨v,hv,hd⟩ := h hs
    have before : s ∈ Ico 0 t := ⟨hs.1,lt_of_le_of_ne hs.2 hsne⟩
    have clipid := clip_eq_self R (prev s before).le
    exact ⟨v,by change v ∈ F (z s); simpa only [G,Function.comp_apply,show realPath p = z from rfl,clipid] using hv,hd⟩
  refine ⟨p,hinit,⟨L,lip⟩,?_⟩
  filter_upwards [inc T] with t ht ht'
  obtain ⟨v,hv,hd⟩ := ht ht'
  have e := clip_eq_self R (confined t ht').le
  exact ⟨v,by change v ∈ F (z t); simpa only [G,Function.comp_apply,show realPath p = z from rfl,e] using hv,hd⟩

end CircleLocalContinuation
