module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! The angular average after folding the two-dimensional hidden direction. -/
@[expose] public section
noncomputable section
namespace CircleFoldedIntegral
open Real Set MeasureTheory
open scoped Interval

theorem folded_integral (s d : ℝ) (hd : 0<d) (small : d<π/2) :
    (∫ θ in -d..d, (1+s^2*(cos θ)^2)⁻¹)/(2*d) =
      arctan (tan d/sqrt (1+s^2))/(d*sqrt (1+s^2)) := by
  let b := sqrt (1+s^2)
  have bp : 0<b := sqrt_pos.mpr (by positivity)
  have bs : b^2=1+s^2 := sq_sqrt (by positivity)
  let F (x : ℝ) := arctan (tan x/b)/b
  have der (x : ℝ) (hx : x∈uIcc (-d) d) :
      HasDerivAt F ((1+s^2*(cos x)^2)⁻¹) x := by
    rw [uIcc_of_le (by linarith)] at hx
    have cp : 0<cos x := cos_pos_of_mem_Ioo ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have dd := ((hasDerivAt_arctan (tan x/b)).comp x ((hasDerivAt_tan cp.ne').div_const b)).div_const b
    apply dd.congr_deriv
    rw [tan_eq_sin_div_cos]
    have den : 0<1+s^2*(cos x)^2 := by positivity
    have den' : 0<(cos x*b)^2+(sin x)^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos (mul_pos cp bp)) (sq_nonneg _)
    field_simp [bp.ne',cp.ne',den.ne',den'.ne']
    nlinarith only [sin_sq_add_cos_sq x,bs,congrArg (fun y : ℝ => y*(cos x)^2) bs]
  have cont : Continuous (fun θ : ℝ => (1+s^2*(cos θ)^2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun x => ne_of_gt (by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt der (cont.intervalIntegrable _ _)]
  simp only [F,tan_neg,neg_div,arctan_neg]
  change (arctan (tan d/b)/b - -(arctan (tan d/b)/b))/(2*d) = arctan (tan d/b)/(d*b)
  ring

end CircleFoldedIntegral
