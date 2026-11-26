module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Path-length estimate for a single neuron with a relative update bound. -/
public section
namespace CircleConfinement

variable {E : Type*} [NormedAddCommGroup E]

/-- If each step is at most `c t` times the current neuron norm, the total
length and the norm are both controlled by the exponential of the prefix sum.
Only steps strictly before the time under consideration are assumed. -/
theorem path_length (z : ℕ → E) (c : ℕ → ℝ) (T : ℕ)
    (nonneg : ∀ t < T, 0 ≤ c t)
    (step : ∀ t < T, ‖z (t+1) - z t‖ ≤ c t * ‖z t‖) :
    ‖z T‖ ≤ ‖z 0‖ * Real.exp (∑ t ∈ Finset.range T, c t) ∧
    ∑ t ∈ Finset.range T, ‖z (t+1) - z t‖ ≤
      ‖z 0‖ * (Real.exp (∑ t ∈ Finset.range T, c t) - 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨hsize, hpath⟩ := ih (fun i hi => nonneg i (Nat.lt_succ_of_lt hi))
      (fun i hi => step i (Nat.lt_succ_of_lt hi))
    let x := ∑ t ∈ Finset.range T, c t
    have inc := (step T (Nat.lt_succ_self T)).trans
      (mul_le_mul_of_nonneg_left hsize (nonneg T (Nat.lt_succ_self T)))
    have hexp : c T + 1 ≤ Real.exp (c T) := Real.add_one_le_exp _
    have growth : (c T + 1) * (‖z 0‖ * Real.exp x) ≤
        Real.exp (c T) * (‖z 0‖ * Real.exp x) := by gcongr
    have tri : ‖z (T+1)‖ ≤ ‖z (T+1)-z T‖ + ‖z T‖ := by
      simpa using norm_add_le (z (T+1)-z T) (z T)
    change ‖z T‖ ≤ ‖z 0‖ * Real.exp x at hsize
    change ‖z (T+1)-z T‖ ≤ c T * (‖z 0‖ * Real.exp x) at inc
    change _ ≤ ‖z 0‖ * (Real.exp x - 1) at hpath
    simp only [Finset.sum_range_succ, Real.exp_add]
    change ‖z (T+1)‖ ≤ ‖z 0‖ * (Real.exp x * Real.exp (c T)) ∧
      _ ≤ ‖z 0‖ * (Real.exp x * Real.exp (c T) - 1)
    constructor <;> linarith

/-- For prefixes with accumulated relative step budget at most one, the
exponential bound is at most twice that budget times the initial norm. -/
theorem small_budget (z : ℕ → E) (c : ℕ → ℝ) (T : ℕ) (b : ℝ)
    (nonneg : ∀ t < T, 0 ≤ c t)
    (step : ∀ t < T, ‖z (t+1) - z t‖ ≤ c t * ‖z t‖)
    (sum_le : ∑ t ∈ Finset.range T, c t ≤ b) (small : b ≤ 1) :
    ∑ t ∈ Finset.range T, ‖z (t+1)-z t‖ ≤ ‖z 0‖ * (2*b) := by
  apply (path_length z c T nonneg step).2.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have pos : 0 ≤ ∑ t ∈ Finset.range T, c t :=
    Finset.sum_nonneg fun i hi => nonneg i (Finset.mem_range.mp hi)
  have := Real.abs_exp_sub_one_le (x := ∑ t ∈ Finset.range T, c t)
    (by simpa only [abs_of_nonneg pos] using sum_le.trans small)
  rw [abs_of_nonneg pos] at this
  linarith [le_abs_self (Real.exp (∑ t ∈ Finset.range T, c t)-1)]

end CircleConfinement
