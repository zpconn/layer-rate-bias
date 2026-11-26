module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Global growth of the discrete parameter path

These bounds apply at every initialization. They use the absolute per-neuron
prediction bound and the per-neuron relative GD step bound from Cauchy–Schwarz.
-/
public section
namespace CircleMoment

variable {m : ℕ}

/-- If each feature is bounded by the hidden weight norm, a single neuron's
absolute output is at most half its combined squared parameter norm. -/
theorem neuron_bound (a h r : ℝ) (cap : |h| ≤ r) :
    |a*h| ≤ (a^2 + r^2)/2 := by
  rw [abs_mul]
  have hmul := mul_le_mul_of_nonneg_left cap (abs_nonneg a)
  have hsq := sq_nonneg (|a| - r)
  nlinarith [sq_abs a]

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def energy (z : Fin m → E) : ℝ := (∑ i, ‖z i‖^2) / m

private theorem energy_nonneg (z : Fin m → E) : 0 ≤ energy z := by
  unfold energy
  positivity

/-- The network has pointwise amplitude bounded by sqrt(m) times half the energy. -/
theorem output_bound (hm : 0 < m) (z : Fin m → E) (parts : Fin m → ℝ)
    (pointwise : ∀ i, |parts i| ≤ ‖z i‖^2 / 2) :
    |(∑ i, parts i) / Real.sqrt m| ≤ Real.sqrt m * energy z / 2 := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have root := Real.sqrt_pos.mpr hm'
  have ha : |∑ i, parts i| ≤ (∑ i, ‖z i‖^2)/2 := calc
    _ ≤ ∑ i, |parts i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖z i‖^2/2 := Finset.sum_le_sum fun i _ ↦ pointwise i
    _ = _ := by rw [Finset.sum_div]
  rw [abs_div, abs_of_pos root, div_le_iff₀ root]
  refine ha.trans_eq ?_
  unfold energy
  field_simp
  nlinarith [Real.sq_sqrt hm'.le, congrArg (fun q : ℝ ↦ (∑ i, ‖z i‖^2) * q) (Real.sq_sqrt hm'.le)]

private theorem energy_growth (z z' : Fin m → E) (g : ℝ)
    (step : ∀ i, ‖z' i‖ ≤ g * ‖z i‖) :
    energy z' ≤ g^2 * energy z := by
  have h (i : Fin m) : ‖z' i‖^2 ≤ g^2 * ‖z i‖^2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (step i) 2
  unfold energy
  rw [← mul_div_assoc, Finset.mul_sum]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ ↦ h i) (Nat.cast_nonneg _)

/-- A unit step bound derived from a loss residual at most sqrt(m) M/2 + 2
gives a cubic bound for the energy plus a fixed offset. -/
theorem global_step (hm : 0 < m) (z z' : Fin m → E)
    (step : ∀ i, ‖z' i - z i‖ ≤ (energy z / 2 + 2 / Real.sqrt m) * ‖z i‖) :
    4 + 2*energy z' ≤ (4+2*energy z)^3 := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hroot : 1 ≤ Real.sqrt m := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hm'
  have hb : 2 / Real.sqrt m ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt m)).2
    linarith
  let M := energy z
  have pos : 0 ≤ M := energy_nonneg z
  have hg (i : Fin m) : ‖z' i‖ ≤ (3+M/2)*‖z i‖ := by
    have h := norm_add_le (z' i-z i) (z i)
    rw [sub_add_cancel] at h
    have hr := (step i).trans (mul_le_mul_of_nonneg_right (add_le_add (a := energy z / 2) le_rfl hb)
      (norm_nonneg (z i)))
    change _ ≤ (3+energy z/2)*‖z i‖
    nlinarith
  have hen := energy_growth z z' (3+M/2) hg
  change _ ≤ (4+2*M)^3
  nlinarith [sq_nonneg M, mul_nonneg (sq_nonneg M) pos]

/-- Uniform-in-the-seed bound at each deterministic cap. -/
theorem path_envelope (hm : 0 < m) (z : ℕ → Fin m → E)
    (step : ∀ t i, ‖z (t+1) i-z t i‖ ≤
      (energy (z t) / 2 + 2 / Real.sqrt m) * ‖z t i‖) (T : ℕ) :
    4+2*energy (z T) ≤ (4+2*energy (z 0))^(3^T) := by
  induction T with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_mul]
    exact (global_step hm _ _ (step t)).trans
      (pow_le_pow_left₀ (by linarith [energy_nonneg (z t)]) ih 3)

open MeasureTheory

/-- The contribution of an exceptional event to the squared error is bounded by its
square-root probability times the square root of the global fourth moment. -/
theorem exceptional_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : MemLp (fun ω ↦ F ω ^ 2) 2 μ) (B : Set Ω) :
    ∫ ω in B, F ω ^ 2 ∂μ ≤
      Real.sqrt (∫ ω, F ω ^ 4 ∂μ) * Real.sqrt (μ.real B) := by
  have conj : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf : MemLp (fun ω ↦ F ω ^ 2) (ENNReal.ofReal 2) (μ.restrict B) := by
    simpa using hF.restrict (s := B)
  have hg : MemLp (fun _ : Ω ↦ (1:ℝ)) (ENNReal.ofReal 2) (μ.restrict B) := memLp_const _
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg conj
    (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (F ω))
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one) hf hg
  have simplify (x : ℝ) : (x ^ 2) ^ (2:ℝ) = x ^ 4 := by norm_cast; ring
  simp only [mul_one, simplify, Real.one_rpow, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ, ← Real.sqrt_eq_rpow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  apply setIntegral_le_integral
  · have hh := hF.integrable_sq
    simpa only [← pow_mul] using hh
  · exact Filter.Eventually.of_forall fun _ ↦ by positivity

end CircleMoment
