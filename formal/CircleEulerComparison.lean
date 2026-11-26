module

public import CircleEulerLimits
public import CircleGaussianTracking
import all CircleGaussianTracking
import Mathlib.Tactic

/-! Divergence comparisons using the actual Gaussian seed measure, ordinary
circle Euler updates, a global Borel Clarke solution and the circle kernel's
equal-rate interpolation weight. -/

@[expose] public section
noncomputable section

namespace CircleEulerComparison
open scoped NNReal
open Filter Topology MeasureTheory ProbabilityTheory
  CircleEscapeBridge CircleSeedIntegrability CircleEulerLimits CircleFlowPath
  CircleFlowMoments CircleInclusionExistence CirclePathSelection

/-- Any same-seed measurable endpoint of a genuine equal-rate flow is
square integrable. Every positive fixed time then gives divergence from that
specific endpoint, under the actual coupling of Euler and continuous time. -/
theorem rms_diverges_from_any_flow (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m)
    (t : ℝ) (ht : 0 < t) (z : Seed m → ℝ → State m) (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) 1 t (z ω))
    (endpoint : Measurable fun ω => z ω t) :
    MemLp (fun ω => mean (z ω t)) 2 (seedLaw m) ∧
    Tendsto (fun k : ℕ => Real.sqrt (∫ ω, (eulerOutput N m t k ω - mean (z ω t))^2 ∂seedLaw m))
      atTop atTop := by
  have gap := (gaussian_flow_fourth (N:=N) (m:=m) (τ:=1) (b:=0) hN (by norm_num)
    (by norm_num) ht.le (by norm_num) (by norm_num) z start flow endpoint).1
  have hY : MemLp (fun ω => mean (z ω t)) 2 (seedLaw m) := by
    have h := (gap.add (reference_memLp N m 0 4 (by norm_num))).mono_exponent (by norm_num : (2:ENNReal) ≤ 4)
    simpa [Pi.add_def] using h
  exact ⟨hY,fixed_time_rms_tendsto N m hN hm t ht _ hY⟩

/-- A single Borel map into whole continuous paths starts from every Gaussian
seed, satisfies the essential limiting-gradient Clarke inclusion for every
finite horizon, and exhibits divergence from Euler at every positive time. -/
theorem exists_selected_flow_with_rms_divergence (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) :
    ∃ f : State m → C(ℝ≥0,State m), @Measurable _ _ inferInstance (borel _) f ∧
      (∀ ω, f ω 0 = ω ∧ ∀ T : ℝ, 0 ≤ T →
        IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) 1 T (realPath (f ω)) ∧
        ∀ᵐ t : ℝ, t ∈ Set.Icc 0 T → ∃ v ∈ essentialGradientHull
          (negativeLossGradient (circleInput N) (circleLabel N) (1/Real.sqrt m) 1) (realPath (f ω) t),
            HasDerivAt (realPath (f ω)) v t) ∧
      ∀ t : ℝ, 0 < t → MemLp (fun ω => mean (realPath (f ω) t)) 2 (seedLaw m) ∧
        Tendsto (fun k : ℕ => Real.sqrt (∫ ω,
          (eulerOutput N m t k ω - mean (realPath (f ω) t))^2 ∂seedLaw m)) atTop atTop := by
  let : MeasurableSpace C(ℝ≥0,State m) := borel _
  have : BorelSpace C(ℝ≥0,State m) := ⟨rfl⟩
  obtain ⟨f,hf,sol⟩ := CircleFlowConstruction.exists_borel_global_clarke_flow N m hN
    (τ:=1) (by norm_num) (by norm_num)
  refine ⟨f,hf,sol,fun t ht => rms_diverges_from_any_flow N m hN hm t ht
    (fun ω => realPath (f ω)) (fun ω => ?_) (fun ω => ((sol ω).2 t ht.le).1) ?_⟩
  · simpa [realPath] using (sol ω).1
  · exact (continuous_eval_const (F:=C(ℝ≥0,State m)) (Real.toNNReal t)).measurable.comp hf

/-- The equal-rate reference weight with the actual grid cardinality as input.
The spectrum indexes a positive cardinality by its predecessor. -/
def interpolationWeight (N : ℕ) := CircleSpectrum.weight 1 (N-1)

theorem interpolationWeight_bounds (N : ℕ) : 0 ≤ interpolationWeight N ∧ interpolationWeight N ≤ 1 :=
  CircleGaussianTracking.weight_bounds (N-1) (by norm_num : (0:ℝ) ≤ 1)

/-- At fixed physical time the RMS discrepancy from the same-seed
deterministic circle kernel reference diverges as well. -/
theorem rms_diverges_from_reference (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k : ℕ => Real.sqrt (∫ ω,
      (eulerOutput N m t k ω-reference N m (interpolationWeight N) ω)^2 ∂seedLaw m)) atTop atTop :=
  fixed_time_rms_tendsto N m hN hm t ht _ (reference_memLp _ _ _ 2 (by norm_num))

/-- Along the growing odd grids the actual same-seed paired MSE of unit-step
GD and the interpolating reference diverges at both published horizons. -/
theorem unit_step_paired_divergence (N : ℕ → ℕ) (grow : Tendsto N atTop atTop) :
    (Tendsto (fun j : ℕ => ∫ ω, (trainedMean (path (N j) (N j^32) 1) ⌈60*Real.log (N j)⌉₊ ω -
      reference (N j) (N j^32) (interpolationWeight (N j)) ω)^2 ∂seedLaw (N j^32)) atTop atTop) ∧
    Tendsto (fun j : ℕ => ∫ ω, (trainedMean (path (N j) (N j^32) 1) (longCap (N j)) ω -
      reference (N j) (N j^32) (interpolationWeight (N j)) ω)^2 ∂seedLaw (N j^32)) atTop atTop := by
  obtain ⟨mid,long⟩ := middle_long_paired_tendsto interpolationWeight interpolationWeight_bounds
  exact ⟨mid.comp grow,long.comp grow⟩

end CircleEulerComparison
