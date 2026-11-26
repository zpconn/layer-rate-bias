module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Exact training-movement budget for a solved linearized least-squares system.
Parameter coordinates and stacked scalar training outputs may have different sizes.
All parameters below have positive initial variance. -/
public section

namespace Movement

variable {P A : Type*} [Fintype P] [Fintype A]

def pullback (J : A → P → ℝ) (u : A → ℝ) (p : P) : ℝ := ∑ a, J a p * u a

def step (J : A → P → ℝ) (rate : P → ℝ) (u : A → ℝ) (p : P) : ℝ :=
  -(rate p * pullback J u p)

def gramAction (J : A → P → ℝ) (rate : P → ℝ) (u : A → ℝ) (a : A) : ℝ :=
  ∑ p, J a p * (rate p * pullback J u p)

/-- The solve hypothesis is J diag(rate) Jᵀ u = r. -/
theorem energy (J : A → P → ℝ) (rate : P → ℝ) (u r : A → ℝ)
    (h : ∀ a, gramAction J rate u a = r a) :
    ∑ p, rate p * (pullback J u p)^2 = ∑ a, r a * u a := by
  simp_rw [← h, gramAction, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  calc
    rate p * (pullback J u p)^2 = (rate p * pullback J u p) * (∑ a, J a p * u a) := by
      change rate p * (pullback J u p)^2 = (rate p * pullback J u p) * pullback J u p
      ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- Nonuniform learning-rate-to-variance ratios weight each energy contribution. -/
theorem heterogeneous (J : A → P → ℝ) (rate var : P → ℝ) (u : A → ℝ) :
    ∑ p, (step J rate u p)^2 / var p =
    ∑ p, (rate p / var p) * (rate p * (pullback J u p)^2) := by
  apply Finset.sum_congr rfl
  intros
  simp only [step, div_eq_mul_inv]
  ring

/-- Sharp interval from coordinatewise bounds on the rate-to-variance ratios. -/
theorem ratio_bounds (J : A → P → ℝ) (rate var : P → ℝ) (u r : A → ℝ)
    (lo hi : ℝ) (rate_nn : ∀ p, 0 ≤ rate p)
    (bounds : ∀ p, lo ≤ rate p / var p ∧ rate p / var p ≤ hi)
    (solve : ∀ a, gramAction J rate u a = r a) :
    lo * (∑ a, r a * u a) ≤ ∑ p, (step J rate u p)^2 / var p ∧
    (∑ p, (step J rate u p)^2 / var p) ≤ hi * ∑ a, r a * u a := by
  rw [heterogeneous, ← energy J rate u r solve, Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_right (bounds p).1
        (mul_nonneg (rate_nn p) (sq_nonneg _))
  · exact Finset.sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_right (bounds p).2
        (mul_nonneg (rate_nn p) (sq_nonneg _))

theorem uniform (J : A → P → ℝ) (rate var : P → ℝ) (u r : A → ℝ) (c : ℝ)
    (positive : ∀ p, 0 < var p) (ratio : ∀ p, rate p = c * var p)
    (solve : ∀ a, gramAction J rate u a = r a) :
    ∑ p, (step J rate u p)^2 / var p = c * ∑ a, r a * u a := by
  rw [heterogeneous, ← energy J rate u r solve, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hc : rate p / var p = c := (div_eq_iff (positive p).ne').2 (ratio p)
  rw [hc]

/-- Sum of an initial residual and the linearized prediction change. -/
def residual (J : A → P → ℝ) (r : A → ℝ) (d : P → ℝ) (a : A) : ℝ :=
  r a + ∑ p, J a p * d p

/-- Parameter displacement for full-batch preconditioned GD, with arbitrary scalar steps. -/
def trajectory (J : A → P → ℝ) (rate : P → ℝ) (r : A → ℝ) (η : ℕ → ℝ) :
    ℕ → P → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun p =>
    let d := trajectory J rate r η n
    d p - η n * rate p * pullback J (residual J r d) p

/-- Integrated residual along the actual linearized iterates. -/
def dualTrajectory (J : A → P → ℝ) (rate : P → ℝ) (r : A → ℝ) (η : ℕ → ℝ) :
    ℕ → A → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun a =>
    dualTrajectory J rate r η n a + η n * residual J r (trajectory J rate r η n) a

omit [Fintype P] in
private theorem pullback_update (J : A → P → ℝ) (u v : A → ℝ) (k : ℝ) (p : P) :
    pullback J (fun a => u a + k * v a) p = pullback J u p + k * pullback J v p := by
  simp only [pullback, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

theorem trajectory_eq_step (J : A → P → ℝ) (rate : P → ℝ) (r : A → ℝ)
    (η : ℕ → ℝ) (n : ℕ) (p : P) :
    trajectory J rate r η n p = step J rate (dualTrajectory J rate r η n) p := by
  induction n with
  | zero => simp [trajectory, step, dualTrajectory, pullback]
  | succ n ih =>
    simp only [trajectory, dualTrajectory, step, pullback_update]
    rw [ih]
    unfold step
    ring

/-- The whitened budget at every finite iterate, with its actual residual reduction. -/
theorem iterate_budget (J : A → P → ℝ) (rate var : P → ℝ) (r : A → ℝ)
    (η : ℕ → ℝ) (n : ℕ) (c : ℝ) (positive : ∀ p, 0 < var p)
    (ratio : ∀ p, rate p = c * var p) :
    ∑ p, (trajectory J rate r η n p)^2 / var p =
    c * ∑ a, (r a - residual J r (trajectory J rate r η n) a) *
      dualTrajectory J rate r η n a := by
  have hs : ∀ a, gramAction J rate (dualTrajectory J rate r η n) a =
      r a - residual J r (trajectory J rate r η n) a := by
    intro a
    simp only [residual, trajectory_eq_step, step, mul_neg, Finset.sum_neg_distrib,
      gramAction]
    ring
  calc
    _ = ∑ p, (step J rate (dualTrajectory J rate r η n) p)^2 / var p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [trajectory_eq_step]
    _ = _ := uniform J rate var _ _ c positive ratio hs

end Movement
