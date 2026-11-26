module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import CircleGridMoments
import all CircleEscape
import Mathlib.Tactic

/-! Positive-part grid margins from centering and isotropic second moments. -/
public section
namespace CircleGridMargin

/-- If grid scores have mean zero, amplitude at most W, and mean square
W²/2, their positive parts have mean at least W/4 and mean square at least
W²/16. The sum formulation also covers the zero vector and the empty grid. -/
theorem relu_sum_bounds {N : ℕ} (v : Fin N → ℝ) (W : ℝ) (nonneg : 0 ≤ W)
    (bound : ∀ i, |v i| ≤ W) (center : ∑ i, v i = 0)
    (second : ∑ i, (v i)^2 = N * W^2 / 2) :
    N * W / 4 ≤ ∑ i, max (v i) 0 ∧
    N * W^2 / 16 ≤ ∑ i, (max (v i) 0)^2 := by
  have each (i : Fin N) : (v i)^2 ≤ W * (2 * max (v i) 0 - v i) := by
    have hh := mul_le_mul_of_nonneg_right (bound i) (abs_nonneg (v i))
    by_cases h : 0 ≤ v i
    · rw [max_eq_left h, abs_of_nonneg h] at *
      nlinarith
    · have hn := le_of_not_ge h
      rw [max_eq_right hn, abs_of_nonpos hn] at *
      nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  rw [second, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, center, sub_zero] at hs
  have mean : N * W / 4 ≤ ∑ i, max (v i) 0 := by
    rcases eq_or_lt_of_le nonneg with h | hp
    · rw [← h]; simpa using Finset.sum_nonneg (s := Finset.univ)
        (fun i _ => le_max_right (v i) 0)
    · apply le_of_mul_le_mul_left (a := W) _ hp
      nlinarith
  refine ⟨mean, ?_⟩
  have lower (i : Fin N) :
      W/2 * max (v i) 0 - W^2/16 ≤ (max (v i) 0)^2 := by
    nlinarith [sq_nonneg (max (v i) 0 - W/4)]
  have sum := Finset.sum_le_sum (s := Finset.univ) fun i _ => lower i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at sum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at sum
  nlinarith [mul_le_mul_of_nonneg_left mean nonneg]

open scoped InnerProductSpace

/-- Both extensive lower bounds for the actual equally spaced circle grid. -/
theorem grid_relu_sum_bounds (N : ℕ) (hN : 3 ≤ N) (w : ℂ) :
    N * ‖w‖ / 4 ≤ ∑ i, CircleEscape.feature w (CircleEscape.gridPoint N i) ∧
    N * ‖w‖^2 / 16 ≤ ∑ i, (CircleEscape.feature w (CircleEscape.gridPoint N i))^2 := by
  apply relu_sum_bounds (fun i ↦ inner ℝ w (CircleEscape.gridPoint N i)) ‖w‖ (norm_nonneg w)
  · intro i
    simpa only [CircleEscape.grid_norm, mul_one] using
      abs_real_inner_le_norm w (CircleEscape.gridPoint N i)
  · exact CircleGridMoments.projection_sum N hN w
  · exact CircleGridMoments.projection_sq_sum N hN w

/-- A unit-radius projection has a ReLU mean of at least 1/4 and a ReLU
second moment of at least 1/16, uniformly in the direction and grid size. -/
theorem grid_relu_mean_bounds (N : ℕ) (hN : 3 ≤ N) (w : ℂ) :
    ‖w‖ / 4 ≤ (∑ i, CircleEscape.feature w (CircleEscape.gridPoint N i)) / N ∧
    ‖w‖^2 / 16 ≤ (∑ i, (CircleEscape.feature w (CircleEscape.gridPoint N i))^2) / N := by
  have np : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨first, second⟩ := grid_relu_sum_bounds N hN w
  exact ⟨(le_div_iff₀ np).2 (by linarith), (le_div_iff₀ np).2 (by linarith)⟩

end CircleGridMargin
