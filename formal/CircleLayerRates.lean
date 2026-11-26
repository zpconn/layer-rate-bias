module

public import CircleSpectrum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! A paired comparison of hidden rates 1/2 and 2. On odd circle grids,
`CircleSpectrum.weight τ n` denotes the interpolation weight at grid size
N=n+1. The paired reference uses exactly the same initial population and
grid means. Bounds on nonlinear flow tracking enter explicitly. -/

public section
noncomputable section

namespace CircleLayerRates
open CircleSpectrum Real Filter Topology MeasureTheory

def reference (population grid weight : ℝ) : ℝ := population - weight*(grid-1)

/-- The shared initial population mean cancels, seed by seed. -/
theorem reference_difference (q grid bslow bfast : ℝ) :
    reference q grid bslow-reference q grid bfast = (bslow-bfast)*(1-grid) := by
  unfold reference
  ring

/-- Derive the paired coefficient by subtracting checked single-rate limits.
The positive sign corresponds to the smaller hidden-learning-rate run first. -/
theorem coefficient_limit :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 * (weight (1/2) n-weight 2 n))
      atTop (𝓝 (π^2/40)) := by
  have h := (bias_limit 2 (by norm_num)).sub (bias_limit (1/2) (by norm_num))
  convert h using 2
  · ring
  · ring

/-- Finite-width pairing in any normed real vector space; taking the space
to be L² of the common seed law controls the paired RMS error. -/
theorem transfer_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ys yf zs zf g : E) (scale b c : ℝ) (hs : 0 ≤ scale)
    (pair : zs-zf = b • g) :
    ‖scale • (ys-yf)-c • g‖ ≤
    scale*(‖ys-zs‖+‖yf-zf‖) + |scale*b-c| * ‖g‖ := by
  have decomp : scale • (ys-yf)-c • g =
      scale • ((ys-zs)-(yf-zf)) + (scale*b-c) • g := by
    rw [sub_smul, mul_smul, ← pair]
    module
  rw [decomp]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs]
  exact add_le_add (mul_le_mul_of_nonneg_left (norm_sub_le (ys-zs) (yf-zf)) hs) le_rfl

/-- Across changing widths and spaces (including a separate seed probability
space for every design), scaled marginal RMS tracking plus a bounded initial
grid statistic imply the paired convergence claim. -/
theorem paired_limit {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    (idx : ℕ → ℕ) (growth : Tendsto idx atTop atTop)
    (ys yf zs zf g : (n : ℕ) → E n) (C : ℝ) (bounded : ∀ n, ‖g n‖ ≤ C)
    (pair : ∀ n, zs n-zf n = (weight (1/2) (idx n)-weight 2 (idx n)) • g n)
    (slow : Tendsto (fun n : ℕ => ((idx n:ℝ)+1)^2*‖ys n-zs n‖) atTop (𝓝 0))
    (fast : Tendsto (fun n : ℕ => ((idx n:ℝ)+1)^2*‖yf n-zf n‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖((idx n:ℝ)+1)^2 • (ys n-yf n)-(π^2/40) • g n‖) atTop (𝓝 0) := by
  let a (n : ℕ) := ((idx n:ℝ)+1)^2
  let e (n : ℕ) := a n*(weight (1/2) (idx n)-weight 2 (idx n))-π^2/40
  have helim : Tendsto (fun n => |e n| * C) atTop (𝓝 0) := by
    convert ((coefficient_limit.comp growth).sub_const (π^2/40)).abs.mul_const C using 2
    · rfl
    · ring_nf
      simp
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    (transfer_bound (ys n) (yf n) (zs n) (zf n) (g n) (a n) _ (π^2/40)
      (sq_nonneg _) (pair n)).trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (bounded n) (abs_nonneg (e n))) _))
  simpa only [a, mul_add, zero_add] using (slow.add fast).add helim

/-- Price incorrect or tied orderings on seeds with absolute initial score at
least `d`. For the layer-rate theorem use `Y=N²(Yslow-Yfast)`, `g=1-grid`
and `c=π²/40`. The probability here is the joint probability of an away-from-tie
seed AND an ordering error. -/
theorem sign_error_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y g : Ω → ℝ) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (E : Set Ω) (hE : MeasurableSet E)
    (wrong : ∀ ω ∈ E, d ≤ |g ω| ∧ g ω * Y ω ≤ 0)
    (int : Integrable (fun ω => (Y ω-c*g ω)^2) μ) :
    μ.real E ≤ (∫ ω, (Y ω-c*g ω)^2 ∂μ)/(c*d)^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (mul_pos hc hd))).mpr
  calc
    _ = ∫ _ in E, (c*d)^2 ∂μ := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ ω in E, (Y ω-c*g ω)^2 ∂μ := by
      apply setIntegral_mono_on (integrable_const _).integrableOn int.integrableOn hE
      intro ω hω
      obtain ⟨away, sign⟩ := wrong ω hω
      have hsq := pow_le_pow_left₀ hd.le away 2
      rw [sq_abs] at hsq
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg c),
        mul_nonpos_of_nonneg_of_nonpos hc.le sign, sq_nonneg (Y ω)]
    _ ≤ _ := setIntegral_le_integral int (ae_of_all _ (fun _ => sq_nonneg _))

end CircleLayerRates
