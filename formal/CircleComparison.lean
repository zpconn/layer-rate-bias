module

public import CircleGaussianTracking
public import CircleEulerComparison
public import CirclePairedCoefficient
import all CirclePairedCoefficient
import all CircleEscapeBridge
public import CircleReferenceMoments
public import CircleStats
import all CircleGaussianTracking
import all CircleFlowMoments
import all CircleActualTracking
import all CircleSpectrum
import Mathlib.Tactic

/-! Bias and seed variance of the trained two-layer network. Each statistic
uses the original product Gaussian law and the actual selected trajectory.

| Experiment | Checked conclusion |
| --- | --- |
| Equal-rate gradient flow, growing odd grid, width N³² and physical time H | `equal_rate_exists` gives unconditioned same-seed tracking, signed bias, variance, and the independent-ensemble MSE. |
| Both layer multipliers on one Gaussian seed at H | `CircleGaussianTracking.exists_paired_actual_tracking` gives joint grid fit and true population tracking. |
| Ordinary unit-step GD, growing grids and both stopping times | `CircleEulerComparison.unit_step_paired_divergence` gives divergent same-seed MSE against the same equal-rate reference. |
| Euler refinement at fixed grid, width and positive physical time | `CircleEulerComparison.exists_selected_flow_with_rms_divergence` constructs a genuine equal-rate flow and proves divergent RMS distance from its same-seed Euler approximation. |
-/
@[expose] public section
noncomputable section
namespace CircleComparison
open Real MeasureTheory ProbabilityTheory Set Filter
open CircleFlowPath CircleFlowMoments CircleFlowTracking CircleTangentDrift CircleEscapeBridge
  CircleGaussianTracking CircleInitializationConcentration
open scoped Topology

/-- Endpoint-measurable actual flow from the Gaussian Cartesian parameter seed. -/
structure Learner (N m : ℕ) (τ : ℝ) where
  path : Seed m → ℝ → State m
  start : ∀ ω, path ω 0 = ω
  flow : ∀ T, 0 ≤ T → ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T (path ω)
  endpoint : ∀ T, 0 ≤ T → Measurable fun ω => path ω T

theorem learner_exists (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2) :
    Nonempty (Learner N m τ) := by
  obtain ⟨z,hz,hs⟩ := exists_actual_selector N m hN hτ h2
  exact ⟨⟨z,hz,fun t ht => (hs t ht).1,fun t ht => (hs t ht).2⟩⟩

abbrev Benchmark (n : ℕ) (τ : ℝ) := Learner (n+1) ((n+1)^32) τ

def trained (n : ℕ) {τ : ℝ} (F : Benchmark n τ) (ω : Seed ((n+1)^32)) :=
  mean (F.path ω (horizon (n+1)))

def matched (n : ℕ) (τ : ℝ) := reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n)

private theorem integrable_pair (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2) (F : Benchmark n τ) :
    MemLp (trained n F) 2 (seedLaw ((n+1)^32)) ∧ MemLp (matched n τ) 2 (seedLaw ((n+1)^32)) := by
  have wb := CircleGaussianTracking.weight_bounds n hτ.le
  have hz := CircleSeedIntegrability.reference_memLp (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) 2 (by norm_num)
  have he := (gaussian_flow_fourth_sharp (Nat.succ_pos n) (pow_pos (Nat.succ_pos n) _) hτ h2
    (Nat.cast_nonneg (horizon (n+1))) wb.1 wb.2 F.path F.start (F.flow _ (Nat.cast_nonneg _))
    (F.endpoint _ (Nat.cast_nonneg _))).1.mono_exponent (by norm_num : (2:ENNReal) ≤ 4)
  refine ⟨?_,hz⟩
  convert he.add hz using 1
  funext ω
  change mean (F.path ω _) = (mean (F.path ω _)-_)+_
  ring

def discrepancyRms (n : ℕ) {τ : ℝ} (F : Benchmark n τ) :=
  sqrt (∫ ω, (trained n F ω - matched n τ ω)^2 ∂seedLaw ((n+1)^32))

def oneRateConstant := pathConstant+horizonMomentConstant*sqrt (sqrt (eventConstant+675))

set_option maxHeartbeats 800000 in
/-- A uniform bound for every fixed multiplier in [1/2,2], including equal
rates. Its constants are independent of the selected trajectory. -/
theorem one_rate_tracking (n : ℕ) (hN : 32 ≤ n+1) (ho : Odd (n+1))
    {τ : ℝ} (hτ : 1/2 ≤ τ) (h2 : τ ≤ 2) (F : Benchmark n τ) :
    discrepancyRms n F ≤ oneRateConstant/(((n:ℝ)+1)^2*sqrt ((n:ℝ)+1)) := by
  let N := n+1
  let μ := seedLaw (N^32)
  obtain ⟨G,mg,gg,miss⟩ := common_good_event N hN
  let bad := {ω | ¬designGood N τ ω}
  let D := toMeasurable μ bad
  let E := G ∩ Dᶜ
  have mE : MeasurableSet E := mg.inter (measurableSet_toMeasurable _ _).compl
  have ht : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have miss₁ : μ.real D ≤ 675/(N:ℝ)^16 := by
    rw [measureReal_def,measure_toMeasurable,← measureReal_def]
    exact designGood_failure hN (by rw [abs_of_pos ht]; exact h2)
  have missE : μ.real Eᶜ ≤ (eventConstant+675)/(N:ℝ)^16 := by
    change μ.real (G ∩ Dᶜ)ᶜ ≤ _
    rw [compl_inter,compl_compl]
    exact ((measureReal_union_le _ _).trans (add_le_add miss miss₁)).trans_eq (by ring)
  have good (ω : Seed (N^32)) (hω : ω ∈ E) :
      |trained n F ω-matched n τ ω| ≤ pathConstant/((n:ℝ)+1)^3 := by
    have hgn := gg ω hω.1
    have ig : designGood N τ ω := Classical.not_not.mp (fun h => hω.2 (subset_toMeasurable μ bad h))
    unfold designGood at ig
    change GoodInit τ _ _ (populationGram (n+1) τ) (populationMeanRow (n+1) τ) ω at ig
    rw [populationGram_sampled] at ig
    simp_rw [show populationMeanRow (n+1) τ = fun _ => CircleSpectrum.k0 τ from funext (populationMeanRow_constant _)] at ig
    have init : ‖CircleActualTracking.gridR (n+1) (F.path ω 0)‖ ≤ ((n:ℝ)+1)^2 := by
      rw [F.start]
      change initialRms N (N^32) ω ≤ _
      simpa only [N,Nat.cast_add,Nat.cast_one] using hgn.2.2.1
    have z := CircleActualTracking.design_endpoint n hN ho τ hτ h2 (F.path ω) (F.flow _ (Nat.cast_nonneg _) ω)
      (by rw [F.start]; simpa only [N,Nat.cast_add,Nat.cast_one,CircleActualTracking.designRadius,CircleActualTracking.designTolerance] using ig)
      init (by rw [F.start]; exact hgn.2.2.2)
    simpa only [trained,matched,pathConstant,F.start] using z.2
  have wb := CircleGaussianTracking.weight_bounds n ht.le
  have h := all_seed_tracking (N:=n+1) (τ:=τ) (b:=CircleSpectrum.weight τ n)
    (B:=pathConstant) (D:=eventConstant+675) (Nat.succ_pos n) ht h2 wb.1 wb.2
    (by unfold pathConstant; positivity) (by unfold eventConstant; positivity) F.path F.start
    (F.flow _ (Nat.cast_nonneg _)) (F.endpoint _ (Nat.cast_nonneg _)) E mE
    (by intro ω hω; simpa only [trained,matched,Nat.cast_add,Nat.cast_one] using good ω hω) missE
  simpa only [discrepancyRms,trained,matched,oneRateConstant,Nat.cast_add,Nat.cast_one] using h

private theorem mean_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y Z : Ω → ℝ} (y : MemLp Y 2 μ) (z : MemLp Z 2 μ) :
    |(∫ ω, Y ω ∂μ) - ∫ ω, Z ω ∂μ| ≤ sqrt (∫ ω, (Y ω-Z ω)^2 ∂μ) := by
  have h := variance_nonneg (Y-Z) μ
  rw [variance_eq_sub (y.sub z)] at h
  rw [← integral_sub (y.integrable (by norm_num)) (z.integrable (by norm_num))]
  apply le_sqrt_of_sq_le
  rw [sq_abs]
  exact sub_nonneg.mp h

private theorem grown (n : ℕ → ℕ) (grow : Tendsto n atTop atTop) :
    Tendsto (fun i => ((n i:ℝ)+1)) atTop atTop :=
  tendsto_atTop_mono (fun i => by linarith : ∀ i, (n i:ℝ) ≤ (n i:ℝ)+1) (tendsto_natCast_atTop_atTop.comp grow)

/-- At arbitrary positive finite widths the exact Gaussian reference
moments transfer to any statistic tracked in RMS at little-o of N⁻². -/
theorem gaussian_reference_transfer (n m : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, 0 < m i) {τ : ℝ} (hτ : 0 ≤ τ)
    (Y : (i : ℕ) → Seed (m i) → ℝ) (hY : ∀ i, MemLp (Y i) 2 (seedLaw (m i)))
    (track : Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (∫ ω,
        (Y i ω-reference (n i+1) (m i) (CircleSpectrum.weight τ (n i)) ω)^2 ∂seedLaw (m i))) atTop (𝓝 0)) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*(1-∫ ω, Y i ω ∂seedLaw (m i))) atTop (𝓝 (π^2*τ/(12*(2+τ)))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (seedLaw (m i)))
      atTop (𝓝 (π^2/360*(1+5*τ^2/(2+τ)^2))) := by
  let D := fun i => (n i:ℝ)+1
  let Z := fun i => reference (n i+1) (m i) (CircleSpectrum.weight τ (n i))
  let μ := fun i => seedLaw (m i)
  let err := fun i => sqrt (∫ ω, (Y i ω-Z i ω)^2 ∂μ i)
  have pair (i : ℕ) : MemLp (Y i) 2 (μ i) ∧ MemLp (Z i) 2 (μ i) :=
    ⟨hY i,CircleSeedIntegrability.reference_memLp _ _ _ 2 (by norm_num)⟩
  have ref := CircleReferenceMoments.reference_limits n m grow hn ho hm τ hτ
  have er : Tendsto (fun i => D i^2*err i) atTop (𝓝 0) := track
  constructor
  · refine ref.1.congr_dist (squeeze_zero (fun i => dist_nonneg) (g:=fun i => D i^2*err i) ?_ er)
    intro i
    rw [dist_comm]
    change dist (D i^2*(1-∫ ω, Y i ω ∂μ i)) (D i^2*(1-∫ ω, Z i ω ∂μ i)) ≤ _
    rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _),sub_sub_sub_cancel_left,abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (mean_transfer (pair i).1 (pair i).2) (sq_nonneg _)
  · let V := π^2/360*(1+5*τ^2/(2+τ)^2)
    have vp : 0 ≤ V := by dsimp [V]; positivity
    have sd (X : (i : ℕ) → Seed (m i) → ℝ) (i : ℕ) :
        sqrt (D i^4*ProbabilityTheory.variance (X i) (μ i)) = D i^2*sqrt (ProbabilityTheory.variance (X i) (μ i)) := by
      rw [sqrt_mul (by positivity),show D i^4=(D i^2)^2 by ring,sqrt_sq (sq_nonneg _)]
    have hz : Tendsto (fun i => D i^2*sqrt (ProbabilityTheory.variance (Z i) (μ i))) atTop (𝓝 (sqrt V)) := by
      simp only [← sd Z]
      exact Real.continuous_sqrt.continuousAt.tendsto.comp ref.2
    have hy : Tendsto (fun i => D i^2*sqrt (ProbabilityTheory.variance (Y i) (μ i))) atTop (𝓝 (sqrt V)) := by
      apply hz.congr_dist (squeeze_zero (fun i => dist_nonneg) (g:=fun i => D i^2*err i) ?_ er)
      intro i
      rw [dist_comm,Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (CircleStats.sd_transfer (pair i).1 (pair i).2) (sq_nonneg _)
    have lim := hy.pow 2
    convert lim using 2 with i
    · dsimp [D,μ]
      rw [mul_pow,sq_sqrt (variance_nonneg _ _)]
      ring
    · exact (sq_sqrt vp).symm


/-- Replacing a stopped kernel coefficient by the interpolation coefficient
costs only its numerical difference times a width-uniform RMS of the
original seed score. No independent copy of the reference is introduced. -/
theorem change_reference_bound {N m : ℕ} (hN : 3 ≤ N) (hm : 0 < m)
    (Y : Seed m → ℝ) (hY : MemLp Y 2 (seedLaw m)) (b b' : ℝ) :
    sqrt (∫ ω, (Y ω-reference N m b ω)^2 ∂seedLaw m) ≤
      sqrt (∫ ω, (Y ω-reference N m b' ω)^2 ∂seedLaw m) +
      |b'-b| * CircleResidualSpectrum.modeConstant := by
  have : NeZero N := ⟨by omega⟩
  let μ := seedLaw m
  let E := Y-reference N m b'
  let V := Y-reference N m b
  let X := CirclePairedCoefficient.score N m
  have he := hY.sub (CircleSeedIntegrability.reference_memLp N m b' 2 (by norm_num))
  have hv := hY.sub (CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num))
  have hx := CirclePairedCoefficient.score_bound (N:=N) hN hm
  have eq : V = E+(b'-b) • X := by
    funext ω
    simp only [V,E,X,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,reference,CirclePairedCoefficient.score]
    ring
  change sqrt (∫ ω, V ω^2 ∂μ) ≤ sqrt (∫ ω, E ω^2 ∂μ)+_
  change MemLp V 2 μ at hv
  change MemLp E 2 μ at he
  rw [CirclePairedCoefficient.rms_of_mem _ hv,CirclePairedCoefficient.rms_of_mem _ he]
  rw [eq]
  apply (lpNorm_add_le he (by norm_num)).trans
  rw [lpNorm_const_smul]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)) _

theorem stopped_reference_transfer (n m : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 3 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) (hm : ∀ i, 0 < m i) {τ : ℝ} (hτ : 0 ≤ τ)
    (Y : (i : ℕ) → Seed (m i) → ℝ) (hY : ∀ i, MemLp (Y i) 2 (seedLaw (m i))) (b' : ℕ → ℝ)
    (stopping : Tendsto (fun i => ((n i:ℝ)+1)^2*|b' i-CircleSpectrum.weight τ (n i)|) atTop (𝓝 0))
    (track : Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (∫ ω,
        (Y i ω-reference (n i+1) (m i) (b' i) ω)^2 ∂seedLaw (m i))) atTop (𝓝 0)) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*(1-∫ ω, Y i ω ∂seedLaw (m i))) atTop (𝓝 (π^2*τ/(12*(2+τ)))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (seedLaw (m i)))
      atTop (𝓝 (π^2/360*(1+5*τ^2/(2+τ)^2))) := by
  apply gaussian_reference_transfer n m grow hn ho hm hτ Y hY
  have limit := track.add (stopping.mul_const CircleResidualSpectrum.modeConstant)
  simp only [zero_mul,add_zero] at limit
  refine squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) (g:=_) ?_ limit
  intro i
  apply (mul_le_mul_of_nonneg_left (change_reference_bound (hn i) (hm i) (Y i) (hY i) _ (b' i))
    (sq_nonneg (((n i:ℝ)+1)))).trans_eq
  ring

/-- Convergence of the bias and variance constants for every actual learner
under the original unconditioned Gaussian seed law and along every growing
odd-grid schedule with N≥33. -/
theorem actual_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 32 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) {τ : ℝ} (hτ : 1/2 ≤ τ) (h2 : τ ≤ 2)
    (F : ∀ i, Benchmark (n i) τ) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*(1-∫ ω, trained (n i) (F i) ω ∂seedLaw ((n i+1)^32)))
      atTop (𝓝 (π^2*τ/(12*(2+τ)))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (trained (n i) (F i)) (seedLaw ((n i+1)^32)))
      atTop (𝓝 (π^2/360*(1+5*τ^2/(2+τ)^2))) := by
  let D := fun i => (n i:ℝ)+1
  have ht : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have pair (i : ℕ) := integrable_pair (n i) ht h2 (F i)
  have dp (i : ℕ) : 0 < D i := by dsimp [D]; positivity
  have er : Tendsto (fun i => D i^2*discrepancyRms (n i) (F i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) (g:=fun i => oneRateConstant*(sqrt (D i))⁻¹)
    · intro i
      have h := one_rate_tracking (n i) (hn i) (ho i) hτ h2 (F i)
      apply (mul_le_mul_of_nonneg_left h (sq_nonneg (D i))).trans
      apply le_of_eq
      change D i^2*(oneRateConstant/(D i^2*sqrt (D i))) = _
      field_simp [(dp i).ne']
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (grown n grow))).const_mul oneRateConstant
  exact gaussian_reference_transfer n (fun i => (n i+1)^32) grow (fun i => by have := hn i; omega)
    ho (fun i => pow_pos (Nat.succ_pos _) _) ht.le (fun i => trained (n i) (F i)) (fun i => (pair i).1) er

/-- At equal layer rates the scaled signed bias is negative, and the scaled
seed variance has the corresponding positive constant. -/
theorem equal_rate_limits (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 32 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) (F : ∀ i, Benchmark (n i) 1) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ ω, trained (n i) (F i) ω ∂seedLaw ((n i+1)^32))-1))
      atTop (𝓝 (-(π^2/36))) ∧
    Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (trained (n i) (F i)) (seedLaw ((n i+1)^32)))
      atTop (𝓝 (7*π^2/1620)) := by
  have h := actual_limits n grow hn ho (τ:=1) (by norm_num) (by norm_num) F
  constructor
  · convert h.1.neg using 2 with i <;> ring
  · convert h.2 using 2
    ring

/-- Equal-rate whole-law RMS tracking itself is little-o of N⁻². -/
theorem equal_rate_tracking_littleO (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 32 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) (F : ∀ i, Benchmark (n i) 1) :
    (fun i => discrepancyRms (n i) (F i)) =o[atTop] (fun i => 1/((n i:ℝ)+1)^2) := by
  have grow' : Tendsto (fun i => n i+1) atTop atTop := tendsto_atTop_mono (fun i => Nat.le_succ _) grow
  have h := tracking_littleO (n:=fun i => n i+1) (err:=fun i => discrepancyRms (n i) (F i)) (C:=oneRateConstant)
    grow' (.of_forall fun i => sqrt_nonneg _) (.of_forall fun i => by
      simpa using one_rate_tracking (n i) (hn i) (ho i) (τ:=1) (by norm_num) (by norm_num) (F i))
  simpa using h


/-- Actual ensemble MSE for r independent Gaussian initializations trained
with the same selected rule. -/
def ensembleMSE (r n : ℕ) (F : Benchmark n 1) :=
  ∫ ω : Fin r → Seed ((n+1)^32), (((r:ℝ)⁻¹)*(∑ j, trained n F (ω j))-1)^2
    ∂(Measure.pi (fun _ : Fin r => seedLaw ((n+1)^32)))

private theorem product_ensemble {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (r : ℕ) (hr : 0 < r) (Y : Ω → ℝ) (hy : MemLp Y 2 μ) (hm : Measurable Y) :
    (∫ ω : Fin r → Ω, ((r:ℝ)⁻¹ * (∑ j, Y (ω j))-1)^2 ∂Measure.pi (fun _ : Fin r => μ)) =
    ((∫ ω, Y ω ∂μ)-1)^2 + ProbabilityTheory.variance Y μ/r := by
  let ν := Measure.pi (fun _ : Fin r => μ)
  let X := fun (j : Fin r) (ω : Fin r → Ω) => Y (ω j)
  have hx (j : Fin r) : MemLp (X j) 2 ν := hy.comp_measurePreserving (measurePreserving_eval _ j)
  have hi : iIndepFun X ν := iIndepFun_pi (X:=fun _ => Y) (fun _ => hm.aemeasurable)
  have hmean (j : Fin r) : ∫ ω, X j ω ∂ν = ∫ ω, Y ω ∂μ :=
    (measurePreserving_eval (fun _ : Fin r => μ) j).hasLaw.integral_comp hy.aestronglyMeasurable
  have hvar (j : Fin r) : ProbabilityTheory.variance (X j) ν = ProbabilityTheory.variance Y μ :=
    (measurePreserving_eval (fun _ : Fin r => μ) j).variance_fun_comp hm.aemeasurable
  have h := CircleInitializationCheck.ensemble_mse ν r hr X hx (fun _ _ hij => hi.indepFun hij)
    (∫ ω, Y ω ∂μ) (ProbabilityTheory.variance Y μ) 1 hmean hvar
  simpa only [Finset.sum_apply,X,ν] using h

theorem ensemble_decomposition (r n : ℕ) (hr : 0 < r) (F : Benchmark n 1) :
    ensembleMSE r n F = ((∫ ω, trained n F ω ∂seedLaw ((n+1)^32))-1)^2 +
      ProbabilityTheory.variance (trained n F) (seedLaw ((n+1)^32))/r :=
  product_ensemble r hr (trained n F) (integrable_pair n (τ:=1) (by norm_num) (by norm_num) F).1
    (CircleFlowMoments.mean_measurable.comp (F.endpoint (horizon (n+1)) (Nat.cast_nonneg _)))

/-- The squared limiting bias survives ensembling while the leading variance
is divided by the number of independent seeds. -/
theorem ensemble_limit (r : ℕ) (hr : 0 < r) (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 32 ≤ n i+1) (ho : ∀ i, Odd (n i+1)) (F : ∀ i, Benchmark (n i) 1) :
    Tendsto (fun i => ((n i:ℝ)+1)^4*ensembleMSE r (n i) (F i)) atTop
      (𝓝 (π^4/1296+7*π^2/(1620*(r:ℝ)))) := by
  have lim := equal_rate_limits n grow hn ho F
  have h := (lim.1.pow 2).add (lim.2.div_const r)
  convert h using 2 with i
  · rw [ensemble_decomposition r (n i) hr (F i)]
    ring
  · ring

/-- Equal-rate limits hold for an actual sequence of global measurable
learners on the complete tail of odd grid sizes. -/
theorem equal_rate_exists :
    ∃ F : ∀ k, Benchmark (oddIndex k) 1,
      ((fun k => discrepancyRms (oddIndex k) (F k)) =o[atTop] (fun k => 1/((oddIndex k:ℝ)+1)^2)) ∧
      Tendsto (fun k => ((oddIndex k:ℝ)+1)^2*((∫ ω, trained (oddIndex k) (F k) ω
        ∂seedLaw ((oddIndex k+1)^32))-1)) atTop (𝓝 (-(π^2/36))) ∧
      Tendsto (fun k => ((oddIndex k:ℝ)+1)^4*ProbabilityTheory.variance (trained (oddIndex k) (F k))
        (seedLaw ((oddIndex k+1)^32))) atTop (𝓝 (7*π^2/1620)) ∧
      ∀ r : ℕ, 0 < r → Tendsto (fun k => ((oddIndex k:ℝ)+1)^4*ensembleMSE r (oddIndex k) (F k)) atTop
        (𝓝 (π^4/1296+7*π^2/(1620*(r:ℝ)))) := by
  have hn (k : ℕ) : 32 ≤ oddIndex k+1 := by unfold oddIndex; omega
  have ho (k : ℕ) : Odd (oddIndex k+1) := ⟨k+16,rfl⟩
  let F (k : ℕ) : Benchmark (oddIndex k) 1 := Classical.choice
    (learner_exists (oddIndex k+1) ((oddIndex k+1)^32) (by have := hn k; omega) (by norm_num) (by norm_num))
  have grow : Tendsto oddIndex atTop atTop := tendsto_atTop_mono (fun k => by change k ≤ 2*(k+16); omega) tendsto_id
  have h := equal_rate_limits oddIndex grow hn ho F
  exact ⟨F,equal_rate_tracking_littleO oddIndex grow hn ho F,h.1,h.2,fun r hr => ensemble_limit r hr oddIndex grow hn ho F⟩

end CircleComparison
