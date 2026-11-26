module

public import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! Variance of a finite-variance output with two measurable, opposite-sign tails. -/
public section

open MeasureTheory ProbabilityTheory
namespace CircleTails

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An event of mass at least p on which the squared deviation exceeds A²
gives the corresponding lower bound on variance. -/
theorem variance_of_deviation_event {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {E : Set Ω} (hE : MeasurableSet E) {p A : ℝ} (hmass : p ≤ μ.real E)
    (htail : ∀ x ∈ E, A ^ 2 ≤ (X x - ∫ y, X y ∂μ) ^ 2) :
    p * A ^ 2 ≤ variance X μ := by
  let c := ∫ y, X y ∂μ
  have hcenter : MemLp (fun x ↦ X x - c) 2 μ := hX.sub (memLp_const c)
  have hint := hcenter.integrable_sq
  rw [variance_eq_integral hX.aemeasurable]
  calc
    p * A ^ 2 ≤ μ.real E * A ^ 2 := mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
    _ = ∫ _ in E, A ^ 2 ∂μ := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in E, (X x - c) ^ 2 ∂μ :=
      setIntegral_mono_on (integrable_const _).integrableOn hint.integrableOn hE htail
    _ ≤ _ := setIntegral_le_integral hint (ae_of_all _ (fun x ↦ sq_nonneg (X x - c)))

/-- Both signs have probability at least p of exceeding magnitude A.
Use the tail opposite the sign of the mean. -/
theorem variance_of_opposite_tails {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {P M : Set Ω} (hP : MeasurableSet P) (hM : MeasurableSet M)
    {p A : ℝ} (hA : 0 ≤ A) (pP : p ≤ μ.real P) (pM : p ≤ μ.real M)
    (upper : ∀ x ∈ P, A ≤ X x) (lower : ∀ x ∈ M, X x ≤ -A) :
    p * A ^ 2 ≤ variance X μ := by
  rcases le_total (∫ y, X y ∂μ) 0 with hc | hc
  · apply variance_of_deviation_event hX hP pP
    intro x hx
    exact pow_le_pow_left₀ hA (by linarith [upper x hx]) 2
  · apply variance_of_deviation_event hX hM pM
    intro x hx
    calc
      A ^ 2 ≤ ((∫ y, X y ∂μ) - X x) ^ 2 :=
        pow_le_pow_left₀ hA (by linarith [lower x hx]) 2
      _ = _ := by ring

end CircleTails
