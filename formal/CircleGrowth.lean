module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

public section
namespace CircleGrowth

/-- One GD step in the large same-sign region, using the projection of the hidden
weight on its previous direction. A and W are the old magnitude and radius. -/
theorem cone_step (A W L s D Wnext : ℝ)
    (hL : 0 < L) (hs : 2*L ≤ s) (hA : s ≤ A) (hW : s ≤ W)
    (hD : 2*A*W^2 ≤ D*L^2)
    (hproject : A*D-W^2 ≤ W*Wnext) :
    s^3/L^2 ≤ D-A ∧ s^3/L^2 ≤ Wnext := by
  have spos : 0 < s := by linarith
  have apos : 0 < A := by linarith
  have wpos : 0 < W := by linarith
  have LS : L^2 ≤ s^2 := by gcongr; linarith
  have LA : L^2 ≤ A^2 := by gcongr; linarith
  have LW : L^2 ≤ W^2 := by gcongr; linarith
  have low₁ : s^3 ≤ A*W^2 := by
    calc s^3 = s*s^2 := by ring
         _ ≤ A*W^2 := by gcongr
  have low₂ : s^3 ≤ A^2*W := by
    calc s^3 = s^2*s := by ring
         _ ≤ A^2*W := by gcongr
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    nlinarith [mul_le_mul_of_nonneg_left LW apos.le]
  · apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    apply le_trans low₂
    apply le_of_mul_le_mul_left (a := W) _ wpos
    have prod := mul_le_mul_of_nonneg_right hproject (sq_nonneg L)
    have dom := mul_le_mul_of_nonneg_left hD apos.le
    nlinarith [mul_le_mul_of_nonneg_right LA (sq_nonneg W)]

/-- Iteration of a cubic lower bound from an initial factor of two. -/
theorem cubic_iteration (x : ℕ → ℝ) (start : 2 ≤ x 0)
    (step : ∀ t, (x t)^3 ≤ x (t+1)) (t : ℕ) : (2:ℝ)^(3^t) ≤ x t := by
  induction t with
  | zero => simpa using start
  | succ t ih =>
    rw [pow_succ, pow_mul]
    exact (pow_le_pow_left₀ (by positivity) ih 3).trans (step t)

open MeasureTheory ProbabilityTheory Set

/-- One coordinate of the explicit large Gaussian initialization box. -/
theorem gaussian_interval_mass (L : ℝ) (hL : 0 ≤ L) :
    L * gaussianPDFReal 0 1 (3*L) ≤
    (gaussianReal 0 1).real (Icc (2*L) (3*L)) := by
  have lower (x : ℝ) (hx : x ∈ Icc (2*L) (3*L)) :
      gaussianPDFReal 0 1 (3*L) ≤ gaussianPDFReal 0 1 x := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hsq : x^2 ≤ (3*L)^2 := by
      have hx0 := hx.1
      gcongr
      · linarith
      · exact hx.2
    linarith
  have bound := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) lower
    (integrable_gaussianPDFReal 0 1).integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at bound
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  convert bound using 2
  ring

/-- Product version for independent standard Gaussian coordinates, with arbitrary
dimension (in the regression model the dimension is three times the width). -/
theorem gaussian_box_mass (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (L * gaussianPDFReal 0 1 (3*L))^k ≤
    (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).real
      (univ.pi (fun _ => Icc (2*L) (3*L))) := by
  simp only [measureReal_def, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  exact pow_le_pow_left₀ (mul_nonneg hL (gaussianPDFReal_nonneg _ _ _))
    (gaussian_interval_mass L hL) k

end CircleGrowth
