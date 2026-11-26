module

public import CircleCapMoments
import all CircleEscape
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleCapInduction
import all CircleCapMoments
import Mathlib.Tactic

/-! A step selected once as a positive multiple of the reciprocal of the
initial top empirical curvature. -/
@[expose] public section
noncomputable section
namespace CircleReciprocal
open Real CircleEscape CircleEscapeBridge CircleCapInduction CircleSeedIntegrability CircleCapMoments

def rate (N m : ℕ) (c : ℝ) (z : Seed m) := c / curvature (gridPoint N) (initial z)

def Y (N m t : ℕ) (c : ℝ) (z : Seed m) :=
  trainedMean (path N m (rate N m c z)) t z

theorem rate_measurable (N m : ℕ) (hN : 3≤N) (odd : Odd N) (hm : 0<m) (c : ℝ) :
    Measurable (rate N m c) := measurable_const.div (curvature_measurable N m hN odd hm)

theorem Y_measurable (N m t : ℕ) (c : ℝ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m) :
    Measurable (Y N m t c) := by
  have hr := rate_measurable N m hN odd hm c
  let path := fun s (ω : Seed m) => CircleInitializationCheck.train N m (rate N m c ω) (initial ω) s
  have meas (s : ℕ) : ∀ j, Measurable (fun ω => (path s ω).a j) ∧
      Measurable (fun ω => (path s ω).w j) := by
    induction s with
    | zero => exact CircleSeedIntegrability.parameter_measurable N m 1 0
    | succ s ih =>
      let u := path s
      let r := fun ω (i : Fin N) => output (1/Real.sqrt m) (u ω) (gridPoint N i) - (1+(gridPoint N i).re)
      have res i : Measurable (fun ω => r ω i) := (CircleSeedIntegrability.output_meas u
        (fun j => (ih j).1) (fun j => (ih j).2) _ _).sub measurable_const
      intro j
      constructor
      · apply (ih j).1.sub
        apply (hr.div measurable_const).mul
        exact Finset.measurable_fun_sum _ fun i _ => (res i).mul
          (CircleSeedIntegrability.feature_meas (ih j).2 _)
      · apply (ih j).2.sub
        apply ((hr.div measurable_const).mul (ih j).1).smul
        exact Finset.measurable_fun_sum _ fun i _ => ((res i).mul
          (CircleSeedIntegrability.gate_meas (ih j).2 _)).smul measurable_const
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ fun j _ => ((meas t j).1).mul (meas t j).2.norm

end CircleReciprocal
