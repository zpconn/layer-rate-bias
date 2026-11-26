module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Discrete-time accounting for the population mean

`r t` is the grid residual, `z t` is the population statistic, and `p` is
its deterministic-kernel interpolation row. `H t` and `g t` include `1/N`
from the loss; for exact nonlinear GD these are the segment-averaged blocks.
The algebra also holds in any norm on the residual space. For the circle,
use an RMS norm so that the unweighted grid average has dual norm one.
-/

public section
namespace CircleDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open MeasureTheory Filter
open scoped Topology InnerProductSpace

private theorem affine_deriv (z dz t : ℝ) :
    HasDerivAt (fun s : ℝ => z + s*dz) dz t := by
  simpa using ((hasDerivAt_id t).mul_const dz).const_add z

/-- Integrating the directional derivative of one unit along a segment updates
both its readout and its feature. A kink on a null set is permitted. -/
theorem feature_segment (a da : ℝ) (f df : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (der : ∀ᵐ t, HasDerivAt f (df t) t) :
    (∫ t in (0:ℝ)..1, da * f t + (a+t*da) * df t) =
      (a+da)*f 1 - a*f 0 := by
  have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => a+t*da) 0 1 :=
    (show ContDiff ℝ 1 (fun t : ℝ => a+t*da) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have eq := hac.integral_deriv_mul_eq_sub hf
  simp only [one_mul, zero_mul, add_zero] at eq
  rw [← eq]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [der] with t ht _
  rw [(affine_deriv _ _ _).deriv, ht.deriv]

/-- Exact update of one ReLU training output, including steps with an activation
crossing and segments lying entirely on the activation boundary. -/
theorem relu_segment (a da z dz : ℝ) :
    (∫ t in (0:ℝ)..1, da * max (z+t*dz) 0 +
      (a+t*da) * (if 0 < z+t*dz then dz else 0)) =
      (a+da)*max (z+dz) 0 - a*max z 0 := by
  let f := fun t : ℝ => z+t*dz
  have hac : AbsolutelyContinuousOnInterval f 0 1 :=
    (show ContDiff ℝ 1 f by dsimp [f]; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hlip : LipschitzWith 1 (fun x : ℝ => max x 0) := LipschitzWith.id.max_const 0
  have hder : ∀ᵐ t, HasDerivAt (fun t => max (f t) 0) (if 0 < f t then dz else 0) t := by
    by_cases hzero : dz = 0
    · subst dz
      simp only [f, mul_zero, add_zero, ite_self]
      exact ae_of_all _ fun t => hasDerivAt_const t _
    · filter_upwards [volume.ae_ne (-z/dz)] with t ht
      have hn : f t ≠ 0 := by
        intro he
        apply ht
        apply (eq_div_iff hzero).mpr
        dsimp [f] at he
        linarith
      have hcont := (affine_deriv z dz t).continuousAt
      rcases lt_or_gt_of_ne hn with h | h
      · rw [ite_eq_right h.not_gt]
        apply (hasDerivAt_const t 0).congr_of_eventuallyEq
        exact (hcont.eventually_lt continuousAt_const h).mono fun u hu => max_eq_right hu.le
      · rw [ite_eq_left h]
        apply (affine_deriv z dz t).congr_of_eventuallyEq
        exact (continuousAt_const.eventually_lt hcont h).mono fun u hu => max_eq_left hu.le
  simpa only [Function.comp_apply, f, zero_mul, one_mul, add_zero] using feature_segment a da _
    (fun t => if 0 < f t then dz else 0) (hlip.comp_absolutelyContinuousOnInterval hac) hder

/-- The population-mean feature of a bias-free circle ReLU unit is proportional
to the norm of its hidden weight. This identity includes steps through zero.
The convention for real division supplies a zero directional term there. -/
theorem radius_segment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a da : ℝ) (w dw : V) :
    (∫ t in (0:ℝ)..1, da * ‖w+t • dw‖ +
      (a+t*da) * (inner ℝ (w+t • dw) dw / ‖w+t • dw‖)) =
      (a+da)*‖w+dw‖ - a*‖w‖ := by
  let f := fun t : ℝ => w+t • dw
  have hft (t : ℝ) : HasDerivAt f dw t := by
    simpa [f] using ((hasDerivAt_id t).smul_const dw).const_add w
  have hac : AbsolutelyContinuousOnInterval f 0 1 :=
    (show ContDiff ℝ 1 f by dsimp [f]; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hder : ∀ᵐ t, HasDerivAt (fun t => ‖f t‖) (inner ℝ (f t) dw / ‖f t‖) t := by
    by_cases hdw : dw = 0
    · subst dw
      simp only [f, smul_zero, add_zero, inner_zero_right, zero_div]
      exact ae_of_all _ fun t => hasDerivAt_const t _
    · have hone : ∀ᵐ t, f t ≠ 0 := by
        by_cases h : ∃ s, f s = 0
        · obtain ⟨s, hs⟩ := h
          filter_upwards [volume.ae_ne s] with t ht he
          have hz : (t-s) • dw = 0 := by
            rw [sub_smul]
            dsimp [f] at hs he
            exact sub_eq_zero.mpr (add_left_cancel (he.trans hs.symm))
          exact (smul_ne_zero (sub_ne_zero.mpr ht) hdw) hz
        · exact ae_of_all _ (fun t he => h ⟨t, he⟩)
      filter_upwards [hone] with t ht
      have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
      have derivSq := (hft t).norm_sq.sqrt (by simpa using hn)
      simpa [Real.sqrt_sq (norm_nonneg _), mul_div_mul_left, hn] using derivSq
  simpa only [Function.comp_apply, f, zero_smul, one_smul, add_zero] using feature_segment a da _
    (fun t => inner ℝ (f t) dw / ‖f t‖)
    (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hac) hder

/-- Signed discrepancy from the same-seed, infinite-time reference. -/
theorem telescope (p : E →L[ℝ] ℝ) (H : ℕ → E →L[ℝ] E) (g : ℕ → E →L[ℝ] ℝ)
    (η : ℝ) (r : ℕ → E) (z : ℕ → ℝ)
    (gridStep : ∀ t, r (t+1) = r t - η • H t (r t))
    (meanStep : ∀ t, z (t+1) = z t - η * g t (r t)) (T : ℕ) :
    z T - (z 0 - p (r 0)) = p (r T) -
      η * ∑ t ∈ Finset.range T, (g t - p.comp (H t)) (r t) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [gridStep, meanStep, Finset.sum_range_succ]
    simp only [map_sub, map_smul, sub_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul] at *
    linarith

/-- A posteriori upper bound using the observed residual path and the dual norm
of the row defect. Taking the absolute value after telescoping retains signs. -/
theorem defect_bound (p : E →L[ℝ] ℝ) (H : ℕ → E →L[ℝ] E) (g : ℕ → E →L[ℝ] ℝ)
    (η : ℝ) (ηpos : 0 ≤ η) (r : ℕ → E) (z : ℕ → ℝ)
    (gridStep : ∀ t, r (t+1) = r t - η • H t (r t))
    (meanStep : ∀ t, z (t+1) = z t - η * g t (r t)) (T : ℕ) :
    |z T - (z 0 - p (r 0))| ≤ |p (r T)| +
      η * ∑ t ∈ Finset.range T, ‖g t - p.comp (H t)‖ * ‖r t‖ := by
  rw [telescope p H g η r z gridStep meanStep T]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg ηpos]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ ηpos
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun t _ => (g t - p.comp (H t)).le_opNorm _

/-- T-step residual contraction from an initial block and a uniform segment-block
error. The contractive condition, when needed, is `ρ + η * δ < 1`. -/
theorem residual_decay (H₀ : E →L[ℝ] E) (H : ℕ → E →L[ℝ] E)
    (η δ ρ : ℝ) (ηpos : 0 ≤ η) (δpos : 0 ≤ δ) (ρpos : 0 ≤ ρ)
    (r : ℕ → E) (gridStep : ∀ t, r (t+1) = r t - η • H t (r t))
    (ideal : ∀ v, ‖v - η • H₀ v‖ ≤ ρ * ‖v‖) (T : ℕ)
    (drift : ∀ t < T, ‖H t - H₀‖ ≤ δ) :
    ‖r T‖ ≤ (ρ + η * δ)^T * ‖r 0‖ := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hh : ‖(H n - H₀) (r n)‖ ≤ δ * ‖r n‖ :=
      ((H n - H₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (drift n (Nat.lt_succ_self _)) (norm_nonneg _))
    have eq : r (n+1) = (r n - η • H₀ (r n)) - η • ((H n - H₀) (r n)) := by
      rw [gridStep, sub_apply, smul_sub]
      abel
    rw [eq, pow_succ']
    calc
      _ ≤ ‖r n - η • H₀ (r n)‖ + ‖η • ((H n - H₀) (r n))‖ := norm_sub_le _ _
      _ ≤ ρ * ‖r n‖ + η * (δ * ‖r n‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ηpos]
        exact add_le_add (ideal _) (mul_le_mul_of_nonneg_left hh ηpos)
      _ = (ρ + η * δ) * ‖r n‖ := by ring
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (ih (fun i hi => drift i (Nat.lt_succ_of_lt hi))) (by positivity)

/-- Deterministic implication used by the full finite-width probability bound.
The empirical normalized grid block may move by at most half the spectral gap
`λ`. The normalized observable row has defect at most `d`. Thus arbitrary
finite-horizon runs satisfying these bounds meet the same-seed reference to
error at most a terminal residual term plus `2 d ‖r₀‖ / λ`. -/
theorem full_training_bound (p : E →L[ℝ] ℝ) (H₀ : E →L[ℝ] E)
    (H : ℕ → E →L[ℝ] E) (g : ℕ → E →L[ℝ] ℝ) (η gap d : ℝ)
    (hη : 0 < η) (hgap : 0 < gap) (hstep : η*gap ≤ 1) (hd : 0 ≤ d)
    (r : ℕ → E) (z : ℕ → ℝ) (T : ℕ)
    (gridStep : ∀ t, r (t+1) = r t - η • H t (r t))
    (meanStep : ∀ t, z (t+1) = z t - η * g t (r t))
    (ideal : ∀ v, ‖v - η • H₀ v‖ ≤ (1-η*gap) * ‖v‖)
    (drift : ∀ t < T, ‖H t - H₀‖ ≤ gap/2)
    (stat : ∀ t < T, ‖g t - p.comp (H t)‖ ≤ d) :
    ‖r T‖ ≤ (1-η*gap/2)^T * ‖r 0‖ ∧
    |z T - (z 0-p (r 0))| ≤
      ‖p‖ * ((1-η*gap/2)^T * ‖r 0‖) + 2*d*‖r 0‖/gap := by
  let q := 1-η*gap/2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have decay (t : ℕ) (ht : t ≤ T) : ‖r t‖ ≤ q^t * ‖r 0‖ := by
    have h := residual_decay H₀ H η (gap/2) (1-η*gap) hη.le (by positivity)
      (sub_nonneg.mpr hstep) r gridStep ideal t (fun i hi => drift i (hi.trans_le ht))
    convert h using 2
    dsimp only [q]
    ring
  have geom : η * (∑ t ∈ Finset.range T, q^t) ≤ 2/gap := by
    apply (le_div_iff₀ hgap).mpr
    have heq := mul_neg_geom_sum q T
    have h1 : 1-q = η*gap/2 := by dsimp [q]; ring
    rw [h1] at heq
    nlinarith [pow_nonneg hq T]
  constructor
  · exact decay T le_rfl
  · apply (defect_bound p H g η hη.le r z gridStep meanStep T).trans
    apply add_le_add
    · exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (decay T le_rfl) (norm_nonneg _))
    · calc
        _ ≤ η * ∑ t ∈ Finset.range T, d * (q^t * ‖r 0‖) := by
          apply mul_le_mul_of_nonneg_left _ hη.le
          apply Finset.sum_le_sum
          intro t ht
          have hlt := Finset.mem_range.mp ht
          exact mul_le_mul (stat t hlt) (decay t hlt.le) (norm_nonneg _) hd
        _ = (η * ∑ t ∈ Finset.range T, q^t) * (d * ‖r 0‖) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          ring
        _ ≤ (2/gap) * (d * ‖r 0‖) :=
          mul_le_mul_of_nonneg_right geom (mul_nonneg hd (norm_nonneg _))
        _ = _ := by ring

/-- Scalar mode solution for the deterministic normalized kernel. There is no
factor depending on the smallest eigenvalue in this expression. -/
theorem constant_mode (avg : E →L[ℝ] ℝ) (H : E →L[ℝ] E) (η γ b : ℝ)
    (r : ℕ → E) (z : ℕ → ℝ) (eigen : ∀ v, avg (H v) = γ * avg v)
    (gridStep : ∀ t, r (t+1) = r t - η • H (r t))
    (meanStep : ∀ t, z (t+1) = z t - η * (b * γ) * avg (r t)) (T : ℕ) :
    avg (r T) = (1-η*γ)^T * avg (r 0) ∧
    z T = z 0 - b * (1 - (1-η*γ)^T) * avg (r 0) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [gridStep, map_sub, map_smul, smul_eq_mul, eigen, meanStep, pow_succ, ih.1, ih.2]
    constructor <;> ring

/-- A finite-horizon bound when a constant mode with unperturbed decay `q`
has additive error at most `d` per step. It also applies when `q = 0`. -/
theorem perturbed_mode (a : ℕ → ℝ) (q d : ℝ) (hq : 0 ≤ q) (T : ℕ)
    (defect : ∀ t < T, |a (t+1) - q * a t| ≤ d) :
    |a T - q^T * a 0| ≤ d * ∑ j ∈ Finset.range T, q^j := by
  induction T with
  | zero => simp
  | succ t ih =>
    specialize ih (fun i hi => defect i (Nat.lt_succ_of_lt hi))
    have eq : a (t+1) - q^(t+1)*a 0 =
        (a (t+1) - q*a t) + q*(a t - q^t*a 0) := by rw [pow_succ']; ring
    rw [eq]
    calc
      _ ≤ |a (t+1) - q * a t| + |q * (a t - q^t * a 0)| := abs_add_le _ _
      _ ≤ d + q * (d * ∑ j ∈ Finset.range t, q^j) := by
        rw [abs_mul, abs_of_nonneg hq]
        exact add_le_add (defect t (Nat.lt_succ_self _)) (mul_le_mul_of_nonneg_left ih hq)
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp only [pow_succ' q, ← Finset.mul_sum, pow_zero]
        ring

/-- The constant mode has a time-uniform perturbation bound with the actual
constant eigenvalue `γ` in the denominator. `H₀` already includes `1/N`.
The bound prices uniform residual size; it does not assume decay at rate `γ`
for arbitrary residuals. -/
theorem mode_drift (avg : E →L[ℝ] ℝ) (H₀ : E →L[ℝ] E) (H : ℕ → E →L[ℝ] E)
    (η γ δ R : ℝ) (hη : 0 < η) (hγ : 0 < γ) (hstep : η*γ ≤ 1)
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (r : ℕ → E) (T : ℕ)
    (eigen : ∀ v, avg (H₀ v) = γ * avg v)
    (gridStep : ∀ t, r (t+1) = r t - η • H t (r t))
    (drift : ∀ t < T, ‖H t - H₀‖ ≤ δ) (bounded : ∀ t < T, ‖r t‖ ≤ R) :
    |avg (r T) - (1-η*γ)^T * avg (r 0)| ≤ ‖avg‖ * δ * R / γ := by
  let q := 1 - η*γ
  have hq : 0 ≤ q := sub_nonneg.mpr hstep
  have hdef (t : ℕ) (ht : t < T) :
      |avg (r (t+1)) - q * avg (r t)| ≤ η * (‖avg‖ * δ * R) := by
    have eq : avg (r (t+1)) - q * avg (r t) = -η * avg ((H t - H₀) (r t)) := by
      rw [gridStep, map_sub, map_smul, smul_eq_mul, sub_apply, map_sub, eigen]
      dsimp [q]
      ring
    have hd := ((H t - H₀).le_opNorm (r t)).trans
      (mul_le_mul (drift t ht) (bounded t ht) (norm_nonneg _) hδ)
    rw [eq, abs_mul, abs_neg, abs_of_pos hη]
    apply mul_le_mul_of_nonneg_left _ hη.le
    rw [mul_assoc]
    exact (avg.le_opNorm _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  have hs := perturbed_mode (fun t => avg (r t)) q _ hq T hdef
  apply hs.trans
  apply (le_div_iff₀ hγ).mpr
  have hsum : (η*γ) * (∑ j ∈ Finset.range T, q^j) ≤ 1 := by
    have h := mul_neg_geom_sum q T
    have e : 1-q = η*γ := by dsimp [q]; ring
    rw [e] at h
    linarith [pow_nonneg hq T]
  calc
    _ = (‖avg‖ * δ * R) * ((η*γ) * ∑ j ∈ Finset.range T, q^j) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg (norm_nonneg _) hδ) hR)

open MeasureTheory

/-- Coupling the trained statistic and its same-seed reference brackets the
trained CDF between two translated reference CDFs, plus the failure probability.
The proof works directly with events under the seed law. -/
theorem cdf_transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (trained reference : Ω → ℝ) (e δ : ℝ)
    (failure : μ.real {ω | e < |trained ω - reference ω|} ≤ δ) (x : ℝ) :
    μ.real {ω | reference ω ≤ x-e} - δ ≤ μ.real {ω | trained ω ≤ x} ∧
    μ.real {ω | trained ω ≤ x} ≤ μ.real {ω | reference ω ≤ x+e} + δ := by
  let bad := {ω | e < |trained ω - reference ω|}
  have cover {A B : Set Ω} (h : A ⊆ B ∪ bad) : μ.real A ≤ μ.real B + δ :=
    (measureReal_mono h).trans ((measureReal_union_le _ _).trans (add_le_add_right failure _))
  constructor
  · apply sub_le_iff_le_add.mpr
    apply cover
    intro ω hw
    change reference ω ≤ x-e at hw
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · change ¬ e < |trained ω - reference ω| at hb
      exact Or.inl (by change trained ω ≤ x; linarith [(abs_le.mp (le_of_not_gt hb)).2])
  · apply cover
    intro ω hw
    change trained ω ≤ x at hw
    by_cases hb : ω ∈ bad
    · exact Or.inr hb
    · change ¬ e < |trained ω - reference ω| at hb
      exact Or.inl (by change reference ω ≤ x+e; linarith [(abs_le.mp (le_of_not_gt hb)).1])

/-- Kolmogorov transfer to any comparison CDF with a density bound `L`. The
comparison and coupling errors add. For a Gaussian of variance `V`, one can
use `L = 1 / sqrt (2 π V)` in the unscaled coordinates. -/
theorem kolmogorov_transfer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (trained reference : Ω → ℝ)
    (G : ℝ → ℝ) (e δ k L : ℝ) (he : 0 ≤ e)
    (failure : μ.real {ω | e < |trained ω-reference ω|} ≤ δ)
    (normal : ∀ x, |μ.real {ω | reference ω ≤ x} - G x| ≤ k)
    (smooth : ∀ a b, |G a - G b| ≤ L * |a-b|) (x : ℝ) :
    |μ.real {ω | trained ω ≤ x} - G x| ≤ k + δ + L*e := by
  obtain ⟨hl, hu⟩ := cdf_transfer μ trained reference e δ failure x
  have h1 := (abs_le.mp (normal (x-e))).1
  have h2 := (abs_le.mp (normal (x+e))).2
  have h3 := (abs_le.mp (smooth (x-e) x)).1
  have h4 := (abs_le.mp (smooth (x+e) x)).2
  rw [show x-e-x = -e by ring, abs_neg, abs_of_nonneg he] at h3
  rw [show x+e-x = e by ring, abs_of_nonneg he] at h4
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CircleDynamics
