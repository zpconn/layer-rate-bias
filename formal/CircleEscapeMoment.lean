module

public import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! A paired second-moment lower bound and a fixed-curvature comparison. -/

public section
open MeasureTheory

namespace CircleEscapeMoment

/-- On an event of mass at least p, a large output and a bounded paired
reference contribute at least p times their squared positive-part gap. -/
theorem paired_second_moment_of_escape
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F Z : Ω → ℝ} (hF : MemLp F 2 μ) (hZ : MemLp Z 2 μ)
    {E : Set Ω} (hE : MeasurableSet E) {p A B : ℝ} (hmass : p ≤ μ.real E)
    (escape : ∀ ω ∈ E, A ≤ |F ω|) (reference : ∀ ω ∈ E, |Z ω| ≤ B) :
    p * (max (A - B) 0)^2 ≤ ∫ ω, (F ω - Z ω)^2 ∂μ := by
  have hint : Integrable (fun ω ↦ (F ω - Z ω)^2) μ := (hF.sub hZ).integrable_sq
  have pointwise (ω : Ω) (hω : ω ∈ E) :
      (max (A - B) 0)^2 ≤ (F ω - Z ω)^2 := by
    have habs : |F ω| ≤ |F ω - Z ω| + |Z ω| := by
      simpa only [sub_add_cancel] using abs_add_le (F ω - Z ω) (Z ω)
    have gap : max (A - B) 0 ≤ |F ω - Z ω| :=
      max_le (by linarith [escape ω hω, reference ω hω]) (abs_nonneg _)
    simpa only [sq_abs] using pow_le_pow_left₀ (le_max_right _ _) gap 2
  calc
    _ ≤ μ.real E * (max (A - B) 0)^2 :=
      mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
    _ = ∫ _ in E, (max (A - B) 0)^2 ∂μ := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ ω in E, (F ω - Z ω)^2 ∂μ :=
      setIntegral_mono_on (integrable_const _).integrableOn hint.integrableOn hE pointwise
    _ ≤ _ := setIntegral_le_integral hint (ae_of_all _ fun ω ↦ sq_nonneg (F ω - Z ω))

/-- A fixed eigencomponent of linearized GD has an explicit geometric
magnitude and grows strictly at every step above the stability threshold. -/
theorem frozen_component_growth (η lam : ℝ) (r : ℕ → ℝ)
    (unstable : 2 < η * lam) (overlap : r 0 ≠ 0)
    (step : ∀ t, r (t + 1) = (1 - η * lam) * r t) (t : ℕ) :
    |r t| = (η * lam - 1)^t * |r 0| ∧ |r t| < |r (t + 1)| := by
  have factor : |1 - η * lam| = η * lam - 1 := by
    rw [abs_of_neg (by linarith : 1 - η * lam < 0)]
    ring
  have mag (n : ℕ) : |r n| = (η * lam - 1)^n * |r 0| := by
    induction n with
    | zero => simp
    | succ n ih => rw [step, abs_mul, factor, ih, pow_succ]; ring
  refine ⟨mag t, ?_⟩
  have positive : 0 < |r t| := by
    rw [mag]
    exact mul_pos (pow_pos (by linarith) _) (abs_pos.mpr overlap)
  rw [step, abs_mul, factor]
  nlinarith [mul_pos (show 0 < η * lam - 2 by linarith) positive]

end CircleEscapeMoment
