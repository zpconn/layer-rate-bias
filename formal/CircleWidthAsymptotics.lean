module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Elementary exponential comparisons used at the critical width. -/
@[expose] public section
noncomputable section
namespace CircleWidthAsymptotics
open Real Filter
open scoped Topology

theorem linear_times_decay {a : ℝ} (ha : 0<a) :
    Tendsto (fun x : ℝ => x*exp (-a*x)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha

theorem eventually_dominates {a b : ℝ} (h : b<a) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C*x*exp (b*x) ≤ exp (a*x)/73728 := by
  have lim := (linear_times_decay (sub_pos.mpr h)).const_mul (73728*C)
  filter_upwards [lim.eventually_le_const (show (73728*C)*0<1 by simp)] with x hx
  have h' := mul_le_mul_of_nonneg_right hx (exp_nonneg (a*x))
  simp only [one_mul] at h'
  have eq : (73728*C*(x*exp (-(a-b)*x)))*exp (a*x)=73728*(C*x*exp (b*x)) := by
    rw [show 73728*C*(x*exp (-(a-b)*x))*exp (a*x) =
       73728*(C*x)*(exp (-(a-b)*x)*exp (a*x)) by ring,← exp_add]; ring_nf
  rw [eq] at h'; linarith

theorem cost_decay {a b : ℝ} (ha : 0<a) (h : b<a) (C : ℝ) :
    Tendsto (fun x : ℝ => exp (C*x*exp (b*x)-exp (a*x)/36864)) atTop (𝓝 0) := by
  have g := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha))
  have d := Real.tendsto_exp_neg_atTop_nhds_zero.comp (g.atTop_mul_const (by norm_num : 0<(73728:ℝ)⁻¹))
  apply squeeze_zero' (Eventually.of_forall fun _ => exp_nonneg _) _ d
  filter_upwards [eventually_dominates h C] with x hx
  apply exp_le_exp.mpr; change _≤ -(exp (a*x)*73728⁻¹); linarith

/-- A polynomial front factor with any fixed real power of eˣ is absorbed
by an exponential penalty in eᵃˣ. -/
theorem simple_cost_decay {a : ℝ} (ha : 0<a) (C : ℝ) :
    Tendsto (fun x : ℝ => exp (C*x-exp (a*x)/36864)) atTop (𝓝 0) := by
  simpa using cost_decay ha ha C

end CircleWidthAsymptotics
