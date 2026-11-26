module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic.Linarith

/-!
# Total variation under a shared randomized channel

The input and output are arbitrary measurable spaces. Mathlib's `tvDist` is the full
variation norm. Dividing by two gives the usual convention for probability laws.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TrainingLaws

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem channel_mono (K : Kernel X Y) {μ ν : Measure X} (h : μ ≤ ν) :
    K ∘ₘ μ ≤ K ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.bind_apply ht K.aemeasurable, Measure.bind_apply ht K.aemeasurable]
  exact lintegral_mono' h le_rfl

/-- A Markov kernel contracts total variation for arbitrary finite input measures. -/
theorem tvDist_channel (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤ tvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  -- The smaller restriction on each side of the Hahn partition is common input mass.
  let ρ := μ.restrict s + ν.restrict sᶜ
  have hμ : ρ ≤ μ := calc
    ρ ≤ μ.restrict s + μ.restrict sᶜ := add_le_add le_rfl hs.ge_on_compl
    _ = μ := Measure.restrict_add_restrict_compl hs.measurableSet
  have hν : ρ ≤ ν := calc
    ρ ≤ ν.restrict s + ν.restrict sᶜ := add_le_add hs.le_on le_rfl
    _ = ν := Measure.restrict_add_restrict_compl hs.measurableSet
  have hm := measureReal_add_measureReal_compl (μ := μ) hs.measurableSet
  have hn := measureReal_add_measureReal_compl (μ := ν) hs.measurableSet
  have hr : ρ.real Set.univ = μ.real s + ν.real sᶜ := by
    simp [ρ, measureReal_add_apply]
  refine (tvDist_triangle _ (K ∘ₘ ρ) _).trans ?_
  rw [tvDist_of_ge (channel_mono K hμ), tvDist_of_le (channel_mono K hν), hs.tvDist_eq]
  simp only [Measure.real, Measure.comp_apply_univ] at *
  linarith

/-- The same bound in the half-variation convention for probability measures. -/
theorem probability_tv_channel (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (K ∘ₘ μ) (K ∘ₘ ν) / 2 ≤ tvDist μ ν / 2 :=
  div_le_div_of_nonneg_right (tvDist_channel K μ ν) (by norm_num)

/-- Applying one common measurable deterministic map is a special case. -/
theorem tvDist_map (f : X → Y) (hf : Measurable f)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  simpa only [Measure.deterministic_comp_eq_map] using
    tvDist_channel (Kernel.deterministic f hf) μ ν

private theorem mass_difference_le (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ.real Set.univ - ν.real Set.univ ≤ tvDist μ ν := by
  have h := tvDist_triangle μ ν 0
  simp only [tvDist_zero_right] at h
  linarith

/-- Every measurable event test has acceptance-probability gap at most half variation. -/
theorem event_gap_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set X} (hs : MeasurableSet s) : |μ.real s - ν.real s| ≤ tvDist μ ν / 2 := by
  have hdiff (p q : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure q] :
      p.real s - q.real s ≤ tvDist p q / 2 := by
    have h₁ := mass_difference_le (p.restrict s) (q.restrict s)
    have h₂ := mass_difference_le (q.restrict sᶜ) (p.restrict sᶜ)
    rw [tvDist_comm] at h₂
    simp only [measureReal_restrict_apply_univ, measureReal_compl hs, probReal_univ] at h₁ h₂
    linarith [tvDist_restrict_add_compl (μ := p) (ν := q) hs]
  have hrev := hdiff ν μ
  rw [tvDist_comm] at hrev
  exact abs_le.mpr ⟨by linarith, hdiff μ ν⟩

/-- Some measurable event attains the half-variation difference for two probability laws. -/
theorem exists_event_attaining (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ s : Set X, MeasurableSet s ∧ ν.real s - μ.real s = tvDist μ ν / 2 := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine ⟨s, hs.measurableSet, ?_⟩
  have h := hs.tvDist_eq
  simp only [measureReal_compl hs.measurableSet, probReal_univ] at h
  linarith

/-- The gap in event-test acceptance after a shared channel obeys the input TV bound. -/
theorem output_event_gap_le (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Y} (hs : MeasurableSet s) :
    |(K ∘ₘ μ).real s - (K ∘ₘ ν).real s| ≤ tvDist μ ν / 2 :=
  (event_gap_le _ _ hs).trans (probability_tv_channel K μ ν)

/-- A measurable property common under one output law also occurs under the other
with an additive loss bounded by the input probability total variation. -/
theorem event_probability_transfer (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Y} (hs : MeasurableSet s) (β : ℝ) (h : 1 - β ≤ (K ∘ₘ ν).real s) :
    1 - β - tvDist μ ν / 2 ≤ (K ∘ₘ μ).real s := by
  have hdiff := (abs_le.mp (output_event_gap_le K μ ν hs)).1
  linarith

/-- Acceptance-probability difference for a two-outcome randomized test. -/
noncomputable def advantage (D : Kernel X Bool) (μ ν : Measure X) : ℝ :=
  |(D ∘ₘ μ).real {true} - (D ∘ₘ ν).real {true}|

/-- Running the channel followed by the test exactly preserves the test's advantage. -/
theorem advantage_comp (K : Kernel X Y) (D : Kernel Y Bool) (μ ν : Measure X) :
    advantage D (K ∘ₘ μ) (K ∘ₘ ν) = advantage (D ∘ₖ K) μ ν := by
  simp only [advantage, Measure.comp_assoc]

/-- Inverse-power definition of negligible for nonnegative advantage sequences. -/
def Negligible (a : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |a n| ≤ 1 / ((n : ℝ) + 1) ^ k

/-- The security parameter is explicit. In a PPT interpretation `tests` is the class
of uniformly efficient randomized test families on a common encoding space. -/
def Indistinguishable (tests : Set (ℕ → Kernel X Bool)) (μ ν : ℕ → Measure X) : Prop :=
  ∀ D ∈ tests, Negligible (fun n ↦ advantage (D n) (μ n) (ν n))

/-- Closure under post-processing relative to a test class. For a complexity-theoretic
instantiation, closure supplies the simulation and runtime bound for composed tests. -/
theorem indistinguishable_channel (K : ℕ → Kernel X Y)
    (inputTests : Set (ℕ → Kernel X Bool)) (outputTests : Set (ℕ → Kernel Y Bool))
    (closed : ∀ D ∈ outputTests, (fun n ↦ D n ∘ₖ K n) ∈ inputTests)
    (μ ν : ℕ → Measure X) (h : Indistinguishable inputTests μ ν) :
    Indistinguishable outputTests (fun n ↦ K n ∘ₘ μ n) (fun n ↦ K n ∘ₘ ν n) := by
  intro D hD
  simpa only [advantage_comp] using h (fun n ↦ D n ∘ₖ K n) (closed D hD)

/-- A standard Gaussian and its reflection have identical endpoint laws even
though this coupling has expected squared movement four in the known coordinate. -/
theorem gaussian_reflection_budget :
    (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1 ∧
    (∫ x : ℝ, (-x - x)^2 ∂gaussianReal 0 1) = 4 := by
  constructor
  · simp [gaussianReal_map_neg]
  · have moment := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable] at moment
    simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at moment
    have pointwise (x : ℝ) : (-x - x)^2 = 4 * x^2 := by ring
    simp_rw [pointwise]
    rw [integral_const_mul, moment, mul_one]

end TrainingLaws
