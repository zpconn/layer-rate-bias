module

public import CircleWeightedDynamics
public import CirclePairedCoefficient
public import CircleSeedIntegrability
import all CircleWeightedDynamics
import all CircleWeightedStep
import all CirclePairedCoefficient
import all CircleTangentDrift
import all CircleFlowPath
import all CircleFlowMoments
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Finite moments of the actual simultaneous gradient-descent iterates.
The constants may depend on the horizon, grid, width, step size and layer rate. -/

@[expose] public section
noncomputable section

namespace CirclePairedGDIntegrable

open MeasureTheory ProbabilityTheory CircleEscapeBridge CircleFlowPath
  CircleTangentDrift CircleWeightedStep

variable {m : ℕ}

private def Moments (f : Seed m → ℝ) : Prop :=
  Measurable f ∧ ∀ p : ENNReal, p ≠ ⊤ → MemLp f p (seedLaw m)

namespace Moments

variable {f g : Seed m → ℝ}

private theorem const (a : ℝ) : Moments (fun _ : Seed m => a) :=
  ⟨measurable_const, fun _ _ => memLp_const _⟩

private theorem coord (i : Coord m) : Moments (fun z : Seed m => z i) := by
  refine ⟨measurable_pi_apply i, fun p hp => ?_⟩
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1) p hp).comp_measurePreserving
    (measurePreserving_eval (fun _ : Coord m => gaussianReal 0 1) i)

private theorem add (hf : Moments f) (hg : Moments g) : Moments (fun z => f z + g z) :=
  ⟨hf.1.add hg.1, fun p hp => (hf.2 p hp).add (hg.2 p hp)⟩

private theorem sub (hf : Moments f) (hg : Moments g) : Moments (fun z => f z - g z) :=
  ⟨hf.1.sub hg.1, fun p hp => (hf.2 p hp).sub (hg.2 p hp)⟩

private theorem mul (hf : Moments f) (hg : Moments g) : Moments (fun z => f z * g z) := by
  refine ⟨hf.1.mul hg.1, fun p hp => ?_⟩
  have : ENNReal.HolderTriple (p * 2) (p * 2) p := by
    constructor
    rw [ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)),
      ←mul_add, ENNReal.HolderTriple.inv_add_inv_eq_inv 2 2 1]
    simp
  have h2 : p * 2 ≠ ⊤ := ENNReal.mul_ne_top hp (by norm_num)
  exact (hf.2 _ h2).mul (hg.2 _ h2)

private theorem sum {ι : Type*} [Fintype ι] {h : ι → Seed m → ℝ} (hh : ∀ i, Moments (h i)) :
    Moments (fun z => ∑ i, h i z) :=
  ⟨Finset.measurable_fun_sum _ (fun i _ => (hh i).1),
    fun p hp => memLp_finsetSum _ (fun i _ => (hh i).2 p hp)⟩

private theorem relu (hf : Moments f) : Moments (fun z => max (f z) 0) := by
  have meas := hf.1.max (measurable_const (a := (0:ℝ)))
  refine ⟨meas, fun p hp => (hf.2 p hp).of_le meas.aestronglyMeasurable ?_⟩
  filter_upwards with z
  change |max (f z) 0| ≤ |f z|
  rw [abs_of_nonneg (le_max_right (f z) 0)]
  exact max_le (le_abs_self _) (abs_nonneg _)

private theorem gate (hf : Moments f) : Moments (fun z => actualGate (f z)) := by
  have meas : Measurable (fun z => actualGate (f z)) :=
    Measurable.ite (measurableSet_lt measurable_const hf.1) measurable_const measurable_const
  refine ⟨meas, fun p _ => MemLp.of_bound meas.aestronglyMeasurable 1 ?_⟩
  filter_upwards with z
  unfold actualGate
  split <;> norm_num

private theorem abs (hf : Moments f) : Moments (fun z => |f z|) :=
  ⟨continuous_abs.measurable.comp hf.1, fun p hp => (hf.2 p hp).abs⟩

private theorem radius (hf : Moments f) (hg : Moments g) :
    Moments (fun z => ‖(⟨f z, g z⟩ : ℂ)‖) := by
  have meas : Measurable (fun z => ‖(⟨f z, g z⟩ : ℂ)‖) := by
    simp_rw [Complex.norm_def,Complex.normSq_apply]
    exact Real.continuous_sqrt.measurable.comp ((hf.1.mul hf.1).add (hg.1.mul hg.1))
  refine ⟨meas, fun p hp => ((hf.abs.add hg.abs).2 p hp).mono' meas.aestronglyMeasurable ?_⟩
  filter_upwards with z
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact Complex.norm_le_abs_re_add_abs_im _

end Moments

private theorem pre_moments {s : Seed m → State m}
    (hs : ∀ i, Moments (fun z => s z i)) (j : Fin m) (x : ℝ × ℝ) :
    Moments (fun z => pre (s z) j x) :=
  ((Moments.const x.1).mul (hs (j,1))).add ((Moments.const x.2).mul (hs (j,2)))

private theorem output_moments {s : Seed m → State m}
    (hs : ∀ i, Moments (fun z => s z i)) (c : ℝ) (x : ℝ × ℝ) :
    Moments (fun z => output c (s z) x) :=
  (Moments.const c).mul (Moments.sum fun j => (hs (j,0)).mul (pre_moments hs j x).relu)

private theorem row_moments {s : Seed m → State m}
    (hs : ∀ i, Moments (fun z => s z i)) (N : ℕ) (i : Fin N) (p : Coord m) (c : ℝ) :
    Moments (fun z => row c (s z) (circleInput N i) (startGates (s z) i) p) := by
  obtain ⟨j,k⟩ := p
  have h := pre_moments hs j (circleInput N i)
  fin_cases k
  · exact (Moments.const c).mul h.relu
  · exact (Moments.const c).mul (((hs (j,0)).mul h.gate).mul (Moments.const (circleInput N i).1))
  · exact (Moments.const c).mul (((hs (j,0)).mul h.gate).mul (Moments.const (circleInput N i).2))

private theorem iterate_moments (τ η : ℝ) (N T : ℕ) (p : Coord m) :
    Moments (fun z : Seed m => iterate τ η N z T p) := by
  induction T generalizing p with
  | zero => exact Moments.coord p
  | succ t ih =>
    let s := fun z : Seed m => iterate τ η N z t
    have hr (i : Fin N) := (output_moments (s := s) ih (1/Real.sqrt m) (circleInput N i)).sub
      (Moments.const (circleLabel N i))
    exact (ih p).add ((Moments.const η).mul ((Moments.const (-rate τ p)).mul
      ((Moments.const (1/(N:ℝ))).mul (Moments.sum fun i =>
        (hr i).mul (row_moments (s := s) ih N i p (1/Real.sqrt m))))))

private theorem mean_moments (τ η : ℝ) (N m T : ℕ) :
    Moments (fun z : Seed m => CircleWeightedDynamics.learnerMean τ η N z T) := by
  let h := iterate_moments (m := m) τ η N T
  exact (Moments.const ((1/Real.sqrt m)/Real.pi)).mul (Moments.sum fun j =>
    (h (j,0)).mul ((h (j,1)).radius (h (j,2))))

/-- Every deterministic finite-step endpoint is a Borel function of its seed. -/
theorem learnerMean_measurable (τ η : ℝ) (N m T : ℕ) :
    Measurable (fun z : Seed m => CircleWeightedDynamics.learnerMean τ η N z T) :=
  (mean_moments τ η N m T).1

/-- Any fixed physical layer rate and global step size give finite moments at each finite cap. -/
theorem learnerMean_memLp (τ η : ℝ) (N m T : ℕ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun z : Seed m => CircleWeightedDynamics.learnerMean τ η N z T) p (seedLaw m) :=
  (mean_moments τ η N m T).2 p hp

private theorem score_moments (N m : ℕ) : Moments (CirclePairedCoefficient.score N m) := by
  unfold CirclePairedCoefficient.score
  simp_rw [← CircleFlowMoments.output_eq_complex, div_eq_mul_inv]
  exact (Moments.const 1).sub ((Moments.sum fun i =>
    output_moments (s := id) Moments.coord (1/Real.sqrt m) (circleInput N i)).mul
      (Moments.const (N:ℝ)⁻¹))

theorem scaledScore_memLp (d : ℝ) (N m : ℕ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun z : Seed m => (d / (N:ℝ)^2) * CirclePairedCoefficient.score N m z) p (seedLaw m) :=
  ((Moments.const (d / (N:ℝ)^2)).mul (score_moments N m)).2 p hp

/-- The difference between two finite-step endpoints on a common seed has all finite moments. -/
theorem contrast_memLp (τ₁ τ₂ η : ℝ) (N m T : ℕ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun z : Seed m => CircleWeightedDynamics.learnerMean τ₁ η N z T -
      CircleWeightedDynamics.learnerMean τ₂ η N z T) p (seedLaw m) :=
  ((mean_moments τ₁ η N m T).sub (mean_moments τ₂ η N m T)).2 p hp

/-- A uniformly bounded coefficient times the initial deficit has bounded RMS. -/
theorem scaledScore_lpNorm_le {N m : ℕ} {d D : ℝ} (hn : 3 ≤ N) (hm : 0 < m) (hd : |d| ≤ D) :
    lpNorm (fun z : Seed m => (d / (N:ℝ)^2) * CirclePairedCoefficient.score N m z) 2
      (seedLaw m) ≤ D * CircleResidualSpectrum.modeConstant := by
  have : NeZero N := ⟨by omega⟩
  have score := CirclePairedCoefficient.score_bound hn hm
  change lpNorm ((d / (N:ℝ)^2) • CirclePairedCoefficient.score N m) 2 _ ≤ _
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (N:ℝ))]
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h2 : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  exact mul_le_mul ((div_le_self (abs_nonneg d) h2).trans hd) score.2 lpNorm_nonneg
    ((abs_nonneg d).trans hd)

/-- A large unconditional second moment survives subtraction of any target of bounded RMS. -/
theorem mse_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {F G : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ x, (F x)^2 ∂μ) / 2 - (lpNorm G 2 μ)^2 ≤ ∫ x, (F x - G x)^2 ∂μ := by
  have diff : Integrable (fun x => (F x-G x)^2) μ := (hF.sub hG).integrable_sq
  have point (x : Ω) : (F x)^2 ≤ (F x-G x)^2 + (G x)^2 + ((F x-G x)^2 + (G x)^2) := by
    nlinarith [sq_nonneg (F x-2*G x)]
  have both : Integrable (fun x => (F x-G x)^2+(G x)^2) μ := diff.add hG.integrable_sq
  have h := integral_mono hF.integrable_sq (both.add both) point
  change (∫ x, (F x)^2 ∂μ) ≤ ∫ x, ((F x-G x)^2+(G x)^2)+((F x-G x)^2+(G x)^2) ∂μ at h
  rw [integral_add both both, integral_add diff hG.integrable_sq] at h
  rw [← CirclePairedCoefficient.rms_of_mem _ hG, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  linarith

end CirclePairedGDIntegrable
