module

public import CircleInclusionExistence
public import CircleLocalContinuation
public import CircleGlobalGluing
import Mathlib.Tactic

/-! A global Borel selection for the Cartesian circle ReLU network, with
the weighted field obtained by convexifying velocities of incident open
activation chambers. The path lives in the compact-open topology on the
entire nonnegative real time axis. -/

@[expose] public section
noncomputable section

namespace CircleFlowConstruction

open Set Metric MeasureTheory CircleFlowPath CirclePathSelection
  CircleInclusionExistence CircleLocalContinuation
open scoped NNReal

/-- A closed support-tested interval on the actual network is an absolutely
continuous weighted flow for the same coordinates and time. -/
theorem flow_of_tests {N m : ℕ} {τ T : ℝ} {p : C(ℝ,State m)}
    (hT : 0 ≤ T) (h : SupportPath (Field N m τ) T p) :
    IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T p ∧
    ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ Field N m τ (p t), HasDerivAt p v t := by
  have reg := circle_chamber_regularity N m (1/Real.sqrt m) τ
  have compact := reg.2.2.1
  obtain ⟨_, hincl⟩ := actual_of_supportPath reg.2.1 (fun z => (reg.1 z).2.2)
    (fun z => (reg.1 z).2.1.isClosed) compact hT h
  obtain ⟨L,hL⟩ := supportPath_lipschitz compact h
  refine ⟨flow_of_derivatives hT (fun k => ?_) hincl, hincl⟩
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
  rw [uIcc_of_le hT]
  exact LipschitzOnWith.of_dist_le_mul fun a ha b hb =>
    (dist_le_pi_dist _ _ k).trans (hL.dist_le_mul a ha b hb)

/-- For odd circle designs in the paper (indeed all grids of size at least
three), shared-state measurable path selection is available for each fixed
positive hidden-layer rate through two, at every width. No path-existence
or path-compactness hypothesis is required. -/
theorem exists_borel_global_flow (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2) :
    ∃ f : State m → C(ℝ≥0,State m), @Measurable _ _ inferInstance (borel _) f ∧
      ∀ x, f x 0 = x ∧ ∀ T : ℝ, 0 ≤ T →
        IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T (realPath (f x)) ∧
        ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ Field N m τ (realPath (f x) t),
          HasDerivAt (realPath (f x)) v t := by
  let : MeasurableSpace C(ℝ≥0,State m) := borel _
  have : BorelSpace C(ℝ≥0,State m) := ⟨rfl⟩
  let F := Field N m τ
  have reg := circle_chamber_regularity N m (1/Real.sqrt m) τ
  have finite (x : State m) (k : ℕ) : ∃ p ∈ testedPrefix F k, p 0 = x := by
    obtain ⟨p, hx, ⟨L,hL⟩, hi⟩ := exists_on_horizon N m hN hτ h2 x (k:ℝ≥0)
    have hreal : LipschitzWith L (realPath p) := by
      change LipschitzWith L (p ∘ Real.toNNReal)
      simpa only [mul_one] using hL.comp Real.lipschitzWith_toNNReal
    exact ⟨p, supportPath_of_inclusion hreal.lipschitzOnWith.absolutelyContinuousOnInterval hi, hx⟩
  have speed (n k : ℕ) : ∃ L : ℝ≥0, ∀ p ∈ testedPrefix F k,
      p 0 ∈ closedBall 0 (n:ℝ) → LipschitzOnWith L p (Iic (k:ℝ≥0)) := by
    obtain ⟨L,hL⟩ := velocity_bound_on_horizon N m hN hτ h2 n k
    refine ⟨L+1, fun p hp hseed => lipschitz_nonnegTime (lipschitz_of_support_bound hp L ?_)⟩
    intro t ht
    have hi : ‖realPath p 0‖ ≤ (n:ℝ≥0) := by simpa [realPath, mem_closedBall] using hseed
    exact hL (realPath p) hi t ht (flow_of_tests ht.1 (supportPath_mono hp ht.2)).1
  obtain ⟨f,hm,hf⟩ := CircleGlobalGluing.measurable_of_prefixes (0:State m) (testedPrefix F)
    (isClosed_prefix reg.2.1) (prefix_nested F) (prefix_local F) finite speed
  refine ⟨f,hm,fun x => ⟨(hf x).1, fun T hT => ?_⟩⟩
  obtain ⟨k, hk⟩ := exists_nat_ge T
  exact flow_of_tests hT (supportPath_mono ((hf x).2 k) hk)

/-- The selected trajectory follows the essential limiting-gradient Clarke
field for the actual empirical loss. The full-measure gradient identification
uses the original Euclidean parameter coordinates and the weighted rates. -/
theorem exists_borel_global_clarke_flow (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ}
    (hτ : 0 < τ) (h2 : τ ≤ 2) :
    ∃ f : State m → C(ℝ≥0,State m), @Measurable _ _ inferInstance (borel _) f ∧
      ∀ x, f x 0 = x ∧ ∀ T : ℝ, 0 ≤ T →
        IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T (realPath (f x)) ∧
        ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ essentialGradientHull
          (negativeLossGradient (circleInput N) (circleLabel N) (1/Real.sqrt m) τ) (realPath (f x) t),
          HasDerivAt (realPath (f x)) v t := by
  obtain ⟨f,hm,hf⟩ := exists_borel_global_flow N m hN hτ h2
  refine ⟨f,hm, fun x => ⟨(hf x).1, fun T hT => ?_⟩⟩
  obtain ⟨flow, incl⟩ := (hf x).2 T hT
  refine ⟨flow, ?_⟩
  filter_upwards [incl] with t ht hab
  obtain ⟨v,hv,hd⟩ := ht hab
  exact ⟨v,(chamberField_eq_essentialGradientHull _ circleInput_ne_zero _ _ _ _ ▸ hv),hd⟩

end CircleFlowConstruction
