module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A finite-run movement estimate

In optimizer coordinates let `A` be the initial Jacobian, `S` its row
space and `B` its Moore–Penrose inverse. The estimate uses the defining
identity `B (A x) = S.starProjection x` and a reference interpolant in `S`.
For gradient descent `delta t` is the actual step and `reference t` is
the step with the same residual and step size but the initial Jacobian.
-/

public section

namespace TrainingPath

open scoped InnerProductSpace

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Projecting the accumulated steps bounds the part outside the row space. -/
theorem leakage (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (u delta reference : ℕ → E) (start : u 0 = 0)
    (next : ∀ t, u (t+1) = u t + delta t) (hmem : ∀ t, reference t ∈ S)
    (T : ℕ) :
    ‖Sᗮ.starProjection (u T)‖ ≤ ∑ t ∈ Finset.range T, ‖delta t - reference t‖ := by
  induction T with
  | zero => simp [start]
  | succ t ih =>
    have href := Submodule.starProjection_orthogonal_apply_eq_zero (hmem t)
    have hstep : Sᗮ.starProjection (delta t) = Sᗮ.starProjection (delta t - reference t) := by
      rw [map_sub, href, sub_zero]
    rw [next, map_add, Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih (hstep ▸ Sᗮ.norm_starProjection_apply_le _))

/-- Squared form of the movement bound. The row-space residual
`A (u T) + r₀` equals the final residual minus the endpoint Taylor remainder. -/
theorem squared_error (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (A : E →L[ℝ] H) (B : H →L[ℝ] E) (project : ∀ x, B (A x) = S.starProjection x)
    (star : E) (r₀ : H) (hstar : star ∈ S) (fit : A star = -r₀)
    (u delta reference : ℕ → E) (start : u 0 = 0)
    (next : ∀ t, u (t+1) = u t + delta t) (hmem : ∀ t, reference t ∈ S)
    (T : ℕ) :
    ‖u T - star‖^2 ≤ (‖B‖ * ‖A (u T) + r₀‖)^2 +
      (∑ t ∈ Finset.range T, ‖delta t - reference t‖)^2 := by
  have hrow : ‖S.starProjection (u T - star)‖ ≤ ‖B‖ * ‖A (u T) + r₀‖ := by
    rw [← project, map_sub A, fit, sub_neg_eq_add]
    exact B.le_opNorm _
  have hnull : ‖Sᗮ.starProjection (u T - star)‖ ≤
      ∑ t ∈ Finset.range T, ‖delta t - reference t‖ := by
    rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hstar, sub_zero]
    exact leakage S u delta reference start next hmem T
  rw [Submodule.norm_sq_eq_add_norm_sq_starProjection (u T - star) S]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hrow 2)
    (pow_le_pow_left₀ (norm_nonneg _) hnull 2)

/-- Application to preconditioned gradient descent in optimizer coordinates.
Here `G t` is the adjoint Jacobian used at step `t` and `G₀` is the initial
adjoint Jacobian. Only their action on the current residual is needed. -/
theorem gd_squared_error (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (A : E →L[ℝ] H) (B : H →L[ℝ] E) (project : ∀ x, B (A x) = S.starProjection x)
    (star : E) (r₀ : H) (hstar : star ∈ S) (fit : A star = -r₀)
    (G : ℕ → H →L[ℝ] E) (G₀ : H →L[ℝ] E) (inRow : ∀ v, G₀ v ∈ S)
    (u : ℕ → E) (r : ℕ → H) (h : ℕ → ℝ) (hn : ∀ t, 0 ≤ h t)
    (start : u 0 = 0) (step : ∀ t, u (t+1) = u t + (-h t) • G t (r t))
    (T : ℕ) :
    ‖u T - star‖^2 ≤ (‖B‖ * ‖A (u T) + r₀‖)^2 +
      (∑ t ∈ Finset.range T, h t * ‖(G t - G₀) (r t)‖)^2 := by
  have bound := squared_error S A B project star r₀ hstar fit u
    (fun t => (-h t) • G t (r t)) (fun t => (-h t) • G₀ (r t))
    start step (fun t => S.smul_mem _ (inRow _)) T
  simpa only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (hn _), sub_apply] using bound

/-- For a fixed linearized model, a strict residual contraction implies
convergence of the original parameter iterates. For ordinary least squares
`G = Aᵀ` and `B = Aᵀ(AAᵀ)⁻¹`, so `B A` fixes the range of `G`. -/
theorem linearized_limit (A : E →L[ℝ] H) (G B : H →L[ℝ] E) (h : ℝ)
    (leftOnGradients : ∀ v, B (A (G v)) = G v)
    (strict : ‖ContinuousLinearMap.id ℝ H - h • A.comp G‖ < 1)
    (r₀ : H) (u : ℕ → E) (start : u 0 = 0)
    (step : ∀ t, u (t+1) = u t - h • G (r₀ + A (u t))) :
    Filter.Tendsto u Filter.atTop (nhds (-B r₀)) := by
  let r (t : ℕ) := r₀ + A (u t)
  let M := ContinuousLinearMap.id ℝ H - h • A.comp G
  have recurse (t : ℕ) : r (t+1) = M (r t) := by
    simp [r, M, step t]
    abel
  have geometric (t : ℕ) : ‖r t‖ ≤ ‖M‖^t * ‖r 0‖ := by
    induction t with
    | zero => simp
    | succ n ih =>
      rw [recurse, pow_succ']
      exact (M.le_opNorm _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih (norm_nonneg M))
  have limr : Filter.Tendsto r Filter.atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) geometric
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg M) strict).mul_const ‖r 0‖
  have fixed (t : ℕ) : B (A (u t)) = u t := by
    induction t with
    | zero => simp [start]
    | succ n ih => simp [step n, ih, leftOnGradients]
  have representation : u = fun t => B (r t) - B r₀ := by
    funext t
    simp [r, fixed]
  rw [representation]
  simpa using ((B.continuous.tendsto 0).comp limr).sub_const (B r₀)

/-- A continuous whitening map carries the iterate limit into the budget limit. -/
theorem squared_budget_limit (C : E →L[ℝ] H) (u : ℕ → E) (x : E)
    (lim : Filter.Tendsto u Filter.atTop (nhds x)) :
    Filter.Tendsto (fun t => ‖C (u t)‖ ^ 2) Filter.atTop (nhds (‖C x‖ ^ 2)) :=
  ((C.continuous.tendsto x).comp lim).norm.pow 2

/-- Conversion to squared energy in a second metric, using its whitening map. -/
theorem budget_error (C : E →L[ℝ] H) (u star : E) (eps : ℝ) (err : ‖u - star‖ ≤ eps) :
    |‖C u‖^2 - ‖C star‖^2| ≤
      2 * ‖C star‖ * (‖C‖ * eps) + (‖C‖ * eps)^2 := by
  have h : |‖C u‖ - ‖C star‖| ≤ ‖C‖ * eps := by
    calc
      _ ≤ ‖C u - C star‖ := abs_norm_sub_norm_le _ _
      _ = ‖C (u-star)‖ := by rw [map_sub]
      _ ≤ ‖C‖ * ‖u-star‖ := C.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left err (norm_nonneg _)
  have hsum : ‖C u‖ + ‖C star‖ ≤ 2 * ‖C star‖ + ‖C‖ * eps := by
    linarith [(abs_le.mp h).2]
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ (‖C‖ * eps) * (2 * ‖C star‖ + ‖C‖ * eps) :=
      by simpa only [mul_comm] using mul_le_mul h hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) ((abs_nonneg _).trans h)
    _ = _ := by ring

end TrainingPath
