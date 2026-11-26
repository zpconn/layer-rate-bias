module

public import CircleFlowPath
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Borel selection of a whole path from the graph of a solution correspondence.
The selection proof constructs countably valued approximants in a complete
compatible metric. Only existence of solutions and compactness of the
restricted solution graphs remain as inputs to the global path theorem. -/

@[expose] public section
noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory Metric
open scoped NNReal

namespace CirclePathSelection

private structure Approximation {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] (F : X → Set Y) (r : ℝ) where
  center : X → Y
  measurable : Measurable center
  near : ∀ x, ∃ y ∈ F x, dist y (center x) < r

/-- Closed-valued measurable selection in a complete separable metric space.
Open-hit measurability concerns the input correspondence, not any selector. -/
theorem exists_measurable_selection {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [CompleteSpace Y] [SeparableSpace Y] [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y]
    (F : X → Set Y) (exists_mem : ∀ x, (F x).Nonempty) (closed : ∀ x, IsClosed (F x))
    (hit : ∀ U : Set Y, IsOpen U → MeasurableSet {x | ∃ y ∈ F x, y ∈ U}) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, f x ∈ F x := by
  classical
  let d := TopologicalSpace.denseSeq Y
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq Y
  let r (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
  have rpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let near (n i : ℕ) (x : X) := ∃ y ∈ F x, y ∈ ball (d i) (r n)
  have near_meas (n i : ℕ) : MeasurableSet {x | near n i x} := hit _ isOpen_ball
  have initial (x : X) : ∃ i, near 0 i x := by
    obtain ⟨y, hy⟩ := exists_mem x
    obtain ⟨i, hi⟩ := hd.exists_dist_lt y (rpos 0)
    exact ⟨i, y, hy, hi⟩
  let start : Approximation F (r 0) :=
    ⟨fun x => d (Nat.find (initial x)),
     measurable_from_nat.comp (measurable_find initial (near_meas 0)),
     fun x => Nat.find_spec (initial x)⟩
  have refine_center (n : ℕ) (a : Approximation F (r n)) :
      ∃ b : Approximation F (r (n+1)), ∀ x, dist (a.center x) (b.center x) ≤ 2 * r n := by
    let good (x : X) (i : ℕ) := near (n+1) i x ∧ dist (a.center x) (d i) < 2 * r n
    have good_exists (x : X) : ∃ i, good x i := by
      obtain ⟨y, hy, hya⟩ := a.near x
      obtain ⟨i, hi⟩ := hd.exists_dist_lt y (rpos (n+1))
      refine ⟨i, ⟨y, hy, hi⟩, (dist_triangle _ y _).trans_lt ?_⟩
      rw [dist_comm (a.center x) y]
      have hstep : r (n+1) = r n * (1/2) := by simp only [r, pow_succ]
      linarith [rpos n]
    have good_meas (i : ℕ) : MeasurableSet {x | good x i} :=
      (near_meas (n+1) i).inter (measurableSet_lt (a.measurable.dist measurable_const)
        measurable_const)
    exact ⟨⟨fun x => d (Nat.find (good_exists x)),
      measurable_from_nat.comp (measurable_find good_exists good_meas),
      fun x => (Nat.find_spec (good_exists x)).1⟩,
      fun x => (Nat.find_spec (good_exists x)).2.le⟩
  let sequence (n : ℕ) : Approximation F (r n) :=
    Nat.rec start (fun k a => (refine_center k a).choose) n
  have step (n : ℕ) (x : X) :
      dist ((sequence n).center x) ((sequence (n+1)).center x) ≤ 2 * r n :=
    (refine_center n (sequence n)).choose_spec x
  have converges (x : X) : ∃ z, Tendsto (fun n => (sequence n).center x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete <| cauchySeq_of_le_geometric (1/2) 2 (by norm_num)
      fun n => step n x
  let f (x : X) := (converges x).choose
  have tends (x : X) : Tendsto (fun n => (sequence n).center x) atTop (𝓝 (f x)) :=
    (converges x).choose_spec
  refine ⟨f, measurable_of_tendsto_metrizable (fun n => (sequence n).measurable)
    (tendsto_pi_nhds.mpr tends), ?_⟩
  intro x
  choose y hy hdist using fun n => (sequence n).near x
  have dist_zero : Tendsto (fun n => dist ((sequence n).center x) (y n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num))
    exact (dist_comm _ _).trans_le (hdist n).le
  exact (closed x).mem_of_tendsto ((tends x).congr_dist dist_zero) (Eventually.of_forall hy)

/-- A relation on seeds and paths has a Borel path selector if its fibers
are nonempty and its graph is compact on each member of a countable cover
of the seed space. The paths may carry any Polish topology, in particular
the topology of locally uniform convergence for global continuous paths. -/
theorem exists_measurable_path {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y] (G : Set (X × Y))
    (B : ℕ → Set X) (cover : ∀ x, ∃ n, x ∈ B n)
    (compact : ∀ n, IsCompact (G ∩ Prod.fst ⁻¹' B n))
    (exists_path : ∀ x, ∃ y, (x,y) ∈ G) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ G := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  let F (x : X) : Set Y := {y | (x,y) ∈ G}
  apply exists_measurable_selection F exists_path
  · intro x
    obtain ⟨n, hn⟩ := cover x
    have h := (compact n).isClosed.preimage (continuous_const.prodMk continuous_id :
      Continuous (fun y : Y => (x, y)))
    simpa [F, preimage_inter, hn, preimage, inter_def] using h
  · intro U hU
    obtain ⟨C, hC, _, hUnion, _⟩ := hU.exists_iUnion_isClosed
    let piece (n k : ℕ) := Prod.fst '' ((G ∩ Prod.fst ⁻¹' B n) ∩ Prod.snd ⁻¹' C k)
    have hpiece (n k : ℕ) : IsCompact (piece n k) :=
      ((compact n).inter_right ((hC k).preimage continuous_snd)).image continuous_fst
    have heq : {x | ∃ y ∈ F x, y ∈ U} = ⋃ n, ⋃ k, piece n k := by
      ext x
      constructor
      · rintro ⟨y, hy, hUmem⟩
        obtain ⟨n, hn⟩ := cover x
        rw [← hUnion, mem_iUnion] at hUmem
        obtain ⟨k,hk⟩ := hUmem
        exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k, (x,y), ⟨⟨hy, hn⟩, hk⟩, rfl⟩⟩
      · intro hx
        obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
        obtain ⟨k, ⟨⟨s, y⟩, ⟨⟨hG, _⟩, hy⟩, rfl⟩⟩ := mem_iUnion.mp hxn
        exact ⟨y, hG, hUnion ▸ mem_iUnion.mpr ⟨k,hy⟩⟩
    rw [heq]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
      (hpiece n k).isClosed.measurableSet


/-- The velocity hull of finitely many incident smooth branches. The labels
can index full-dimensional activation regions and the cells their closures. -/
def incidentHull {ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (cell : ι → Set X) (velocity : ι → X → E) (x : X) : Set E :=
  convexHull ℝ ((fun i => velocity i x) '' {i | x ∈ cell i})

/-- The graph of the incident velocity hull is closed, including when several
activation boundaries meet. A strictly separating linear functional persists
locally on the finitely many incident branches. -/
theorem isClosed_incident_graph {ι X E : Type*} [Finite ι] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (cell : ι → Set X) (velocity : ι → X → E)
    (hcell : ∀ i, IsClosed (cell i)) (hv : ∀ i, Continuous (velocity i)) :
    IsClosed {q : X × E | q.2 ∈ incidentHull cell velocity q.1} := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨x,v⟩ hxv
  let values := (fun i => velocity i x) '' {i | x ∈ cell i}
  have hfin : values.Finite := (Set.toFinite _).image _
  obtain ⟨l, a, below, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ values) (hfin.isCompact_convexHull ℝ).isClosed hxv
  let U (i : ι) : Set (X × E) :=
    Prod.fst ⁻¹' (cell i)ᶜ ∪ {q | l (velocity i q.1) < a}
  have hU (i : ι) : IsOpen (U i) := ((hcell i).isOpen_compl.preimage continuous_fst).union
    (isOpen_lt (l.continuous.comp ((hv i).comp continuous_fst)) continuous_const)
  refine ⟨{q : X × E | a < l q.2} ∩ ⋂ i, U i, ?_, ?_, ?_⟩
  · rintro ⟨z,w⟩ ⟨hlo, hupper⟩ hw
    have hgen : ((fun i => velocity i z) '' {i | z ∈ cell i}) ⊆ {b | l b < a} := by
      rintro _ ⟨i, hi, rfl⟩
      exact (Set.mem_iInter.mp hupper i).resolve_left (not_not.mpr hi)
    have hlow : a < l w := hlo
    have hhigh : l w < a := convexHull_min hgen (convex_halfSpace_lt l.toLinearMap.isLinear a) hw
    exact (lt_asymm hlow) hhigh
  · exact (isOpen_lt continuous_const (l.continuous.comp continuous_snd)).inter
      (isOpen_iInter_of_finite hU)
  · refine ⟨above, Set.mem_iInter.mpr fun i => ?_⟩
    by_cases hi : x ∈ cell i
    · exact Or.inr (below _ (subset_convexHull ℝ values ⟨i, hi, rfl⟩))
    · exact Or.inl hi

/-- Over a compact set of states, the incident velocity graph is compact in
a proper state space. In particular its velocities are bounded there. -/
theorem isCompact_incident_graph {ι X E : Type*} [Finite ι] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (cell : ι → Set X) (velocity : ι → X → E)
    (hcell : ∀ i, IsClosed (cell i)) (hv : ∀ i, Continuous (velocity i))
    (K : Set X) (hK : IsCompact K) :
    IsCompact ({q : X × E | q.2 ∈ incidentHull cell velocity q.1} ∩ Prod.fst ⁻¹' K) := by
  let V := ⋃ i, velocity i '' K
  have hV : IsCompact V := isCompact_iUnion fun i => hK.image (hv i)
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:E)).mp hV.isBounded
  have hball (x : X) (hx : x ∈ K) : incidentHull cell velocity x ⊆ closedBall 0 r := by
    apply convexHull_min _ (convex_closedBall 0 r)
    rintro _ ⟨i, _, rfl⟩
    exact ball_subset_closedBall (hr (mem_iUnion.mpr ⟨i, x, hx, rfl⟩))
  have hsub := (hK.prod (isCompact_closedBall (0:E) r)).inter_left
    (isClosed_incident_graph cell velocity hcell hv)
  convert hsub using 1
  ext ⟨x,v⟩
  exact ⟨fun h => ⟨h.1, h.2, hball x h.2 h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- The incident hull is upper hemicontinuous: a neighborhood of the full
fiber at a state contains the full fibers at all sufficiently nearby states. -/
theorem upperHemicontinuous_incidentHull {ι X E : Type*} [Finite ι] [MetricSpace X]
    [ProperSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (cell : ι → Set X) (velocity : ι → X → E)
    (hcell : ∀ i, IsClosed (cell i)) (hv : ∀ i, Continuous (velocity i)) :
    UpperHemicontinuous (incidentHull cell velocity) := by
  apply UpperHemicontinuous.of_forall_isOpen
  intro x U hU hx
  let G : Set (X × E) := {q | q.2 ∈ incidentHull cell velocity q.1}
  let K := closedBall x (1:ℝ)
  let bad := Prod.fst '' ((G ∩ Prod.fst ⁻¹' K) ∩ Prod.snd ⁻¹' Uᶜ)
  have hb : IsCompact bad :=
    ((isCompact_incident_graph cell velocity hcell hv K (isCompact_closedBall _ _)).inter_right
      (hU.isClosed_compl.preimage continuous_snd)).image continuous_fst
  have outside : x ∈ badᶜ := by
    rintro ⟨⟨z,v⟩, ⟨⟨hfield, _⟩, hbad⟩, rfl⟩
    exact hbad (hx hfield)
  filter_upwards [hb.isClosed.isOpen_compl.mem_nhds outside,
      closedBall_mem_nhds x (zero_lt_one : (0:ℝ) < 1)] with z hz hzK
  intro v hv
  by_contra h
  exact hz ⟨(z,v), ⟨⟨hv, hzK⟩, h⟩, rfl⟩

/-- A Borel admissible velocity exists on the original state space when
the closed incidence cells cover it. -/
theorem exists_measurable_incident_velocity {ι X E : Type*} [Finite ι]
    [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] (o : X)
    (cell : ι → Set X) (velocity : ι → X → E)
    (hcell : ∀ i, IsClosed (cell i)) (hv : ∀ i, Continuous (velocity i))
    (cover : ∀ x, ∃ i, x ∈ cell i) :
    ∃ v : X → E, Measurable v ∧ ∀ x, v x ∈ incidentHull cell velocity x := by
  apply exists_measurable_path {q | q.2 ∈ incidentHull cell velocity q.1}
    (fun n => closedBall o (n:ℝ)) (fun x => exists_nat_ge (dist x o))
    (fun _ => isCompact_incident_graph cell velocity hcell hv _ (isCompact_closedBall _ _))
  intro x
  obtain ⟨i, hi⟩ := cover x
  exact ⟨velocity i x, subset_convexHull ℝ _ ⟨i,hi,rfl⟩⟩

section ActivationCells

open CircleFlowPath

variable {N m : ℕ}

/-- An open activation chamber on the training grid. Only nonempty chambers
can contribute limiting branch velocities through the closure below. -/
def strictCell (x : Fin N → ℝ × ℝ) (s : Fin N → Fin m → Bool) : Set (State m) :=
  {z | ∀ i j, if s i j then 0 < pre z j (x i) else pre z j (x i) < 0}

private theorem continuous_pre (j : Fin m) (u : ℝ × ℝ) :
    Continuous (fun z : State m => pre z j u) := by unfold pre; fun_prop

theorem isOpen_strictCell (x : Fin N → ℝ × ℝ) (s : Fin N → Fin m → Bool) :
    IsOpen (strictCell x s) := by
  simp only [strictCell, Set.ofPred_forall]
  apply isOpen_iInter_of_finite; intro i
  apply isOpen_iInter_of_finite; intro j
  cases h : s i j
  · exact isOpen_lt (continuous_pre j _) continuous_const
  · exact isOpen_lt continuous_const (continuous_pre j _)

private theorem continuous_branch (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ)
    (s : Fin N → Fin m → Bool) : Continuous (fun z => branchVelocity x y c τ z s) := by
  have hrow (i : Fin N) (p : Coord m) :
      Continuous (fun z => row c z (x i) (fun j => if s i j then 1 else 0) p) := by
    rcases p with ⟨j,k⟩
    fin_cases k <;> cases hs : s i j <;> simp [row, pre, hs] <;> fun_prop
  have hr (i : Fin N) : Continuous (fun z : State m => residual x y c z i) := by
    unfold CircleFlowPath.residual output pre
    fun_prop
  apply continuous_pi
  intro p
  unfold branchVelocity velocity gradient
  fun_prop

/-- The field uses jointly realizable incident gate patterns. Independent
choices at simultaneous zero preactivations could include spurious patterns. -/
def chamberField (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ) :
    State m → Set (State m) :=
  incidentHull (fun s => closure (strictCell x s)) (fun s z => branchVelocity x y c τ z s)

theorem chamberField_subset_incident (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ)
    (z : State m) : chamberField x y c τ z ⊆ incidentField x y c τ z := by
  apply convexHull_mono
  apply Set.image_mono
  intro s hs i j
  cases h : s i j
  · apply closure_minimal (t := {z | pre z j (x i) ≤ 0}) ?_
      (isClosed_le (continuous_pre j _) continuous_const) hs
    intro z hz
    have hh : pre z j (x i) < 0 := by simpa [h] using hz i j
    exact hh.le
  · apply closure_minimal (t := {z | 0 ≤ pre z j (x i)}) ?_
      (isClosed_le continuous_const (continuous_pre j _)) hs
    intro z hz
    have hh : 0 < pre z j (x i) := by simpa [h] using hz i j
    exact hh.le

/-- At a nonzero training direction each gate-zero hyperplane has empty
interior. All gates can simultaneously be made strict arbitrarily close to
a prescribed seed. Finiteness then gives at least one incident open chamber. -/
theorem exists_incident_chamber (x : Fin N → ℝ × ℝ) (hx : ∀ i, x i ≠ 0) (z : State m) :
    ∃ s, z ∈ closure (strictCell x s) := by
  classical
  let nz (q : Fin N × Fin m) : Set (State m) := {u | pre u q.2 (x q.1) ≠ 0}
  have ho (q : Fin N × Fin m) : IsOpen (nz q) :=
    isOpen_ne_fun (continuous_pre _ _) continuous_const
  have hd (q : Fin N × Fin m) : Dense (nz q) := by
    let l : State m →ₗ[ℝ] ℝ :=
      (x q.1).1 • LinearMap.proj (R := ℝ) (q.2,1) + (x q.1).2 • LinearMap.proj (R := ℝ) (q.2,2)
    change Dense ((LinearMap.ker l : Set (State m))ᶜ)
    rw [← interior_eq_empty_iff_dense_compl]
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hi
    have htop := (LinearMap.ker l).eq_top_of_nonempty_interior' hi
    have hl := LinearMap.ker_eq_top.mp htop
    have h1 := LinearMap.congr_fun hl (fun p : Coord m => if p.2 = 1 then (1:ℝ) else 0)
    have h2 := LinearMap.congr_fun hl (fun p : Coord m => if p.2 = 2 then (1:ℝ) else 0)
    apply hx q.1
    ext
    · simpa [l] using h1
    · simpa [l] using h2
  have hunion : Dense (⋃ s : Fin N → Fin m → Bool, strictCell x s) :=
    (dense_iInter_of_isOpen ho hd).mono (by
      intro v hv
      apply mem_iUnion.mpr
      refine ⟨fun i j => decide (0 < pre v j (x i)), ?_⟩
      intro i j
      have hn : pre v j (x i) ≠ 0 := mem_iInter.mp hv (i,j)
      by_cases h : 0 < pre v j (x i)
      · simp [h]
      · simpa [h] using lt_of_le_of_ne (le_of_not_gt h) hn)
  have hz := hunion z
  rw [closure_iUnion_of_finite] at hz
  exact mem_iUnion.mp hz

theorem circleInput_ne_zero (i : Fin N) : circleInput N i ≠ 0 := by
  intro hi
  have hz : CircleEscape.gridPoint N i = 0 :=
    Complex.ext (congrArg Prod.fst hi) (congrArg Prod.snd hi)
  simpa [hz] using CircleEscape.grid_norm N i

/-- The actual chamber field for the ReLU circle grid has compact convex
nonempty values, upper hemicontinuity, a compact state/velocity graph over
each compact state set, and a Borel velocity selector. -/
theorem circle_chamber_regularity (N m : ℕ) (c τ : ℝ) :
    let F := chamberField (m := m) (circleInput N) (circleLabel N) c τ
    (∀ z, (F z).Nonempty ∧ IsCompact (F z) ∧ Convex ℝ (F z)) ∧
    UpperHemicontinuous F ∧
    (∀ K : Set (State m), IsCompact K → IsCompact ({q : State m × State m | q.2 ∈ F q.1} ∩
      Prod.fst ⁻¹' K)) ∧ (∃ v : State m → State m, Measurable v ∧ ∀ z, v z ∈ F z) := by
  dsimp only
  let cell := fun s : Fin N → Fin m → Bool => closure (strictCell (circleInput N) s)
  let vel := fun (s : Fin N → Fin m → Bool) (z : State m) => branchVelocity (circleInput N) (circleLabel N) c τ z s
  have hcell (s) : IsClosed (cell s) := isClosed_closure
  have hvel (s) : Continuous (vel s) := continuous_branch _ _ _ _ _
  have cover (z : State m) : ∃ s, z ∈ cell s := exists_incident_chamber _ circleInput_ne_zero z
  refine ⟨?_, upperHemicontinuous_incidentHull cell vel hcell hvel,
    isCompact_incident_graph cell vel hcell hvel,
    exists_measurable_incident_velocity 0 cell vel hcell hvel cover⟩
  intro z
  obtain ⟨s, hs⟩ := cover z
  let V := (fun i => vel i z) '' {i | z ∈ cell i}
  have hf : V.Finite := (toFinite _).image _
  exact ⟨⟨vel s z, subset_convexHull ℝ V ⟨s, hs, rfl⟩⟩,
    hf.isCompact_convexHull ℝ, convex_convexHull ℝ V⟩

/-- Outside a Lebesgue-null union of training hyperplanes, the circle
parameters belong to a strict chamber. -/
theorem strict_cells_ae (x : Fin N → ℝ × ℝ) (hx : ∀ i, x i ≠ 0) :
    ∀ᵐ z : State m, ∃ s, z ∈ strictCell x s := by
  have avoid (q : Fin N × Fin m) : ∀ᵐ z : State m, pre z q.2 (x q.1) ≠ 0 := by
    let l : State m →ₗ[ℝ] ℝ :=
      (x q.1).1 • LinearMap.proj (R := ℝ) (q.2,1) + (x q.1).2 • LinearMap.proj (R := ℝ) (q.2,2)
    have hker : LinearMap.ker l ≠ ⊤ := by
      intro h
      have hl := LinearMap.ker_eq_top.mp h
      have h1 := LinearMap.congr_fun hl (fun p : Coord m => if p.2 = 1 then (1:ℝ) else 0)
      have h2 := LinearMap.congr_fun hl (fun p : Coord m => if p.2 = 2 then (1:ℝ) else 0)
      apply hx q.1
      apply Prod.ext
      · simpa [l] using h1
      · simpa [l] using h2
    rw [ae_iff]
    simp only [not_not]
    have eq : {a : State m | pre a q.2 (x q.1) = 0} = (LinearMap.ker l : Set (State m)) := by
      ext a
      simp [l,pre,LinearMap.mem_ker]
    rw [eq]
    exact Measure.addHaar_submodule volume (LinearMap.ker l) hker
  filter_upwards [ae_all_iff.mpr avoid] with z hz
  refine ⟨fun i j => decide (0 < pre z j (x i)), ?_⟩
  intro i j
  by_cases h : 0 < pre z j (x i)
  · simp [h]
  · simpa [h] using lt_of_le_of_ne (le_of_not_gt h) (hz (i,j))

/-- The actual weighted negative gradient in Cartesian coordinates at a smooth
point. Its arbitrary definition at nonsmooth points disappears in the
essential limiting-gradient formula. -/
def negativeLossGradient (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ)
    (z : State m) : State m :=
  fun p => -(rate τ p) * fderiv ℝ (fun q => loss (CircleFlowPath.residual x y c q)) z (Pi.single p 1)

/-- The Clarke field written as the intersection over Lebesgue-null exceptional
sets of convex hulls of limiting weighted negative gradients. A closure in
the joint state/velocity space takes limits with both variables convergent. -/
def essentialGradientHull {m : ℕ} (g : State m → State m) (z : State m) : Set (State m) :=
  ⋂ B : Set (State m), ⋂ (_ : volume B = 0),
    convexHull ℝ {v | (z,v) ∈ closure ((fun u => (u,g u)) '' Bᶜ)}

private theorem closure_graph_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {v : X → Y} (hv : Continuous v) (S : Set X) :
    closure ((fun x => (x,v x)) '' S) = (fun x => (x,v x)) '' closure S := by
  apply le_antisymm _ (image_closure_subset_closure_image (continuous_id.prodMk hv))
  let D : Set (X × Y) := (Prod.fst ⁻¹' closure S) ∩ {q | v q.1 = q.2}
  have hD : IsClosed D := (isClosed_closure.preimage continuous_fst).inter
    (isClosed_eq (hv.comp continuous_fst) continuous_snd)
  have hsub : (fun x => (x,v x)) '' S ⊆ D := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨subset_closure hx,rfl⟩
  rintro ⟨x,y⟩ h
  have hx := closure_minimal hsub hD h
  exact ⟨x,hx.1,Prod.ext rfl hx.2⟩

/-- The finite incident chamber hull agrees exactly with the essential
limiting-gradient definition of the weighted Clarke velocity field. The
identity is unchanged by excluding any additional Lebesgue-null set. -/
theorem chamberField_eq_essentialGradientHull (x : Fin N → ℝ × ℝ) (hx : ∀ i, x i ≠ 0)
    (y : Fin N → ℝ) (c τ : ℝ) (z : State m) :
    chamberField x y c τ z = essentialGradientHull (negativeLossGradient x y c τ) z := by
  classical
  let g := negativeLossGradient (m := m) x y c τ
  let v := fun (s : Fin N → Fin m → Bool) (w : State m) => branchVelocity x y c τ w s
  have agree (s : Fin N → Fin m → Bool) (u : State m) (hu : u ∈ strictCell x s) : v s u = g u :=
    funext (branchVelocity_eq_neg_fderiv x y c τ u s hu)
  have cont (s) : Continuous (v s) := continuous_branch x y c τ s
  apply le_antisymm
  · intro w hw
    simp only [essentialGradientHull, mem_iInter]
    intro B hb
    apply convexHull_mono _ hw
    rintro _ ⟨s,hs,rfl⟩
    have hB : Dense Bᶜ := Measure.dense_of_ae (μ := volume) (by simpa [ae_iff] using hb)
    have hnear : z ∈ closure (strictCell x s ∩ Bᶜ) :=
      closure_minimal (hB.open_subset_closure_inter (isOpen_strictCell x s)) isClosed_closure hs
    have hz : (z, v s z) ∈ closure ((fun u => (u,v s u)) '' (strictCell x s ∩ Bᶜ)) :=
      image_closure_subset_closure_image (continuous_id.prodMk (cont s)) ⟨z,hnear,rfl⟩
    apply closure_mono _ hz
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,hu.2,Prod.ext rfl (agree s u hu.1).symm⟩
  · intro w hw
    let good := ⋃ s : Fin N → Fin m → Bool, strictCell x s
    have hgood : volume goodᶜ = 0 := by
      have h := strict_cells_ae (m := m) x hx
      have hm : ∀ᵐ z : State m, z ∈ good := h.mono fun _ hz => mem_iUnion.mpr hz
      exact ae_iff.mp hm
    have hmem := mem_iInter.mp (mem_iInter.mp hw goodᶜ) hgood
    simp only [compl_compl] at hmem
    apply convexHull_mono _ hmem
    intro v' h'
    have heq : (fun u => (u,g u)) '' good =
        ⋃ s, (fun u => (u,v s u)) '' strictCell x s := by
      rw [show good = ⋃ s, strictCell x s from rfl, Set.image_iUnion]
      apply iUnion_congr
      intro s
      exact Set.image_congr fun u hu => Prod.ext rfl (agree s u hu).symm
    change (z,v') ∈ closure ((fun u => (u,g u)) '' good) at h'
    rw [heq, closure_iUnion_of_finite] at h'
    obtain ⟨s,hs⟩ := mem_iUnion.mp h'
    rw [closure_graph_image (cont s)] at hs
    obtain ⟨u,hu,he⟩ := hs
    obtain rfl : u = z := congrArg Prod.fst he
    exact ⟨s,hu,congrArg Prod.snd he⟩

end ActivationCells

/-- A closed family of global paths with bounded initial values and one
Lipschitz constant on each finite interval is compact for local uniform
convergence. Its pointwise compact bounds follow from the speed bound. -/
theorem isCompact_global_paths {E : Type*} [MetricSpace E] [ProperSpace E]
    (A : Set C(ℝ≥0, E)) (closed : IsClosed A) (o : E) (r : ℝ)
    (initial : ∀ p ∈ A, p 0 ∈ closedBall o r)
    (speed : ∀ T : ℝ≥0, ∃ L : ℝ≥0, ∀ p ∈ A, LipschitzOnWith L p (Iic T)) :
    IsCompact A := by
  have hclosedEmb : IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact : C(ℝ≥0, E) → _) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  rw [← closed.closure_eq]
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun p : C(ℝ≥0, E) => (p : ℝ≥0 → E))
    (𝔖 := {K | IsCompact K}) (fun _ h => h) hclosedEmb
  · intro K hK
    obtain ⟨T, hT⟩ := IsCompact.bddAbove hK
    obtain ⟨L, hL⟩ := speed T
    exact (LipschitzOnWith.uniformEquicontinuousOn _ L fun p : A =>
      (hL p.1 p.2).mono hT).equicontinuousOn
  · intro K _ t _
    obtain ⟨L, hL⟩ := speed t
    refine ⟨closedBall o (L * dist t 0 + r), isCompact_closedBall _ _, ?_⟩
    intro p hp
    exact (dist_triangle (p t) (p 0) o).trans
      (add_le_add ((hL p hp).dist_le_mul t (show t ∈ Iic t from le_rfl)
        0 (show (0 : ℝ≥0) ≤ t from t.2)) (initial p hp))

/-- For continuous trajectories on the full nonnegative time axis, the
compact-graph hypotheses follow from closedness of the solution family and
a shared finite Lipschitz bound on each bounded time interval for seeds in
each bounded ball. The same Lipschitz bound also gives pointwise precompactness
in the proper state space. -/
theorem exists_measurable_global_trajectory {E : Type*} [MetricSpace E] [ProperSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    (o : E) (S : Set C(ℝ≥0, E)) (closed : IsClosed S)
    (exists_solution : ∀ x : E, ∃ p ∈ S, p 0 = x)
    (speed : ∀ (n : ℕ) (T : ℝ≥0), ∃ L : ℝ≥0, ∀ p ∈ S,
      p 0 ∈ closedBall o (n : ℝ) → LipschitzOnWith L p (Iic T)) :
    ∃ f : E → C(ℝ≥0, E), Measurable f ∧ ∀ x, f x ∈ S ∧ f x 0 = x := by
  let : Nonempty E := ⟨o⟩
  let : Nonempty C(ℝ≥0, E) := ⟨ContinuousMap.const _ o⟩
  let B (n : ℕ) := closedBall o (n : ℝ)
  let A (n : ℕ) := S ∩ (fun p : C(ℝ≥0, E) => p 0) ⁻¹' B n
  have compact_paths (n : ℕ) : IsCompact (A n) :=
    isCompact_global_paths _ (closed.inter (isClosed_closedBall.preimage (continuous_eval_const 0)))
      o n (fun _ hp => hp.2) fun T => by
        obtain ⟨L, hL⟩ := speed n T
        exact ⟨L, fun p hp => hL p hp.1 hp.2⟩
  let G : Set (E × C(ℝ≥0, E)) := {q | q.2 ∈ S ∧ q.2 0 = q.1}
  apply exists_measurable_path G B
  · intro x
    exact exists_nat_ge (dist x o)
  · intro n
    have heq : G ∩ Prod.fst ⁻¹' B n =
        (fun p : C(ℝ≥0, E) => (p 0, p)) '' A n := by
      ext ⟨x, p⟩
      constructor
      · rintro ⟨⟨hp, he⟩, hx⟩
        obtain rfl : p 0 = x := he
        exact ⟨p, ⟨hp, hx⟩, rfl⟩
      · rintro ⟨q, hq, h⟩
        cases h
        exact ⟨⟨hq.1, rfl⟩, hq.2⟩
    rw [heq]
    exact (compact_paths n).image ((continuous_eval_const 0).prodMk continuous_id)
  · exact exists_solution

/-- A global trajectory exists if each finite-horizon predicate has a
witness starting at the seed, the predicates are closed and nested, and
the witnesses can be chosen with common local Lipschitz bounds. The
witnesses need not agree on overlaps or be measurable in the seed. -/
theorem exists_global_of_finite_horizons {E : Type*} [MetricSpace E] [ProperSpace E]
    (x : E) (P : ℕ → Set C(ℝ≥0, E)) (closed : ∀ n, IsClosed (P n))
    (nested : ∀ n, P (n+1) ⊆ P n) (L : ℝ≥0 → ℝ≥0)
    (finite_solution : ∀ n, ∃ p ∈ P n, p 0 = x ∧ ∀ T, LipschitzOnWith (L T) p (Iic T)) :
    ∃ p : C(ℝ≥0, E), p 0 = x ∧ ∀ n, p ∈ P n := by
  let A : Set C(ℝ≥0, E) := {p | p 0 = x} ∩ ⋂ T : ℝ≥0, {p | LipschitzOnWith (L T) p (Iic T)}
  have hA : IsClosed A := by
    apply (isClosed_eq (continuous_eval_const 0) continuous_const).inter
    apply isClosed_iInter
    intro T
    exact (isClosed_setOfPred_lipschitzOnWith (L T) (Iic T)).preimage
      (continuous_pi fun t => (continuous_eval_const t : Continuous (fun p : C(ℝ≥0,E) => p t)))
  have cA : IsCompact A := isCompact_global_paths A hA x 0
    (fun p hp => by
      have hx : p 0 = x := hp.1
      simp [hx])
    (fun T => ⟨L T, fun _ hp => Set.mem_iInter.mp hp.2 T⟩)
  obtain ⟨p,hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => A ∩ P n) (fun n p hp => ⟨hp.1, nested n hp.2⟩)
    (fun n => by
      obtain ⟨p,hp,hx,hL⟩ := finite_solution n
      exact ⟨p, ⟨hx, Set.mem_iInter.mpr hL⟩, hp⟩)
    (cA.inter_right (closed 0)) (fun n => hA.inter (closed n))
  exact ⟨p, (Set.mem_iInter.mp hp 0).1.1, fun n => (Set.mem_iInter.mp hp n).2⟩

end CirclePathSelection
