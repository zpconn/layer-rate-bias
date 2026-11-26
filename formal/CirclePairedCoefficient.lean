module

public import CircleGaussianTracking
public import CircleResidualSpectrum
public import CircleLayerRates
import all CircleGaussianTracking
import all CircleResidualSpectrum
import all CircleFlowMoments
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Paired nonlinear layer-rate coefficient for actual full-gradient flows on the same Gaussian seed. -/
public section
noncomputable section
namespace CirclePairedCoefficient
open CircleFlowTracking CircleGaussianTracking CircleFlowMoments CircleFlowPath CircleEscapeBridge CircleSpectrum
  CircleResidualSpectrum MeasureTheory ProbabilityTheory Real Filter Topology Finset

/-- Physical seed statistic that distinguishes the two layer rates. -/
def score (N m : ℕ) (ω : Seed m) : ℝ :=
  1-(∑ i, CircleEscape.output (1/√(m:ℝ)) (initial ω) (CircleEscape.gridPoint N i))/N

private theorem zero_mode {N m : ℕ} [NeZero N] (hn : 3≤N) (ω : Seed m) :
    (initialCoeff N m 0 ω).re = -score N m ω := by
  have h0 := CircleGridMoments.projection_sum N hn 1
  simp [Complex.inner] at h0
  change (∑ i, (CircleEscape.gridPoint N i).re)=0 at h0
  simp only [initialCoeff,ZMod.dft_apply,mul_zero,neg_zero,AddChar.map_zero_eq_one,one_smul,Complex.div_natCast_re,
    Complex.re_sum,Complex.ofReal_re]
  let a (i : Fin N) := CircleEscape.output (1/√(m:ℝ)) (initial ω) (CircleEscape.gridPoint N i)-(1+(CircleEscape.gridPoint N i).re)
  change (∑ i, a ((ZMod.finEquiv N).symm.toEquiv i))/N = _
  rw [Equiv.sum_comp]
  unfold a
  simp only [score,Finset.sum_sub_distrib,Finset.sum_add_distrib,h0,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,add_zero]
  field_simp [NeZero.ne (N:ℝ)]
  ring

private theorem score_bound {N m : ℕ} [NeZero N] (hn : 3≤N) (hm : 0<m) :
    MemLp (score N m) 2 (seedLaw m) ∧ lpNorm (score N m) 2 (seedLaw m) ≤ modeConstant := by
  let f := initialCoeff N m 0
  have hf := initialCoeff_uniform hm (0:ZMod N)
  have hf2 : MemLp f 2 (seedLaw m) := hf.1.mono_exponent (by norm_num)
  have eq : score N m = fun ω => -Complex.reCLM (f ω) := by funext ω;simpa [f] using (congrArg Neg.neg (zero_mode hn ω)).symm
  have hm2 : MemLp (score N m) 2 (seedLaw m) := by rw [eq];exact (hf2.continuousLinearMap_comp Complex.reCLM).neg
  refine ⟨hm2,?_⟩
  have h (ω : Seed m) : ‖score N m ω‖≤‖f ω‖ := by rw [eq, norm_neg];exact Complex.abs_re_le_norm _
  calc
    _ ≤ lpNorm (fun ω => ‖f ω‖) 2 (seedLaw m) := lpNorm_mono_real hf2.norm h
    _ = lpNorm f 2 (seedLaw m) := lpNorm_norm hf2.aestronglyMeasurable _
    _ ≤ lpNorm f 4 (seedLaw m) := by rw [←toReal_eLpNorm,←toReal_eLpNorm];exact ENNReal.toReal_mono hf.1.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    _ ≤ _ := hf.2

private theorem rms_of_mem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    √(∫ ω, f ω^2 ∂μ) = lpNorm f 2 μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,Real.sqrt_eq_rpow]
  norm_num [Real.norm_eq_abs,sq_abs,one_div]

def endpoint (n : ℕ) (z : Family (n+1)) (q : Bool) (ω : Seed ((n+1)^32)) := mean (z q ω (horizon (n+1)))

def pairedError (n : ℕ) (z : Family (n+1)) (ω : Seed ((n+1)^32)) :=
  ((n:ℝ)+1)^2*(endpoint n z false ω-endpoint n z true ω)-(π^2/40)*score (n+1) ((n+1)^32) ω

private theorem paired_estimate (n : ℕ) (hn : 3≤n+1) (z : Family (n+1))
    (hm : ∀ q, MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32))) :
    √(∫ ω, pairedError n z ω ^2 ∂seedLaw ((n+1)^32)) ≤
    ((n:ℝ)+1)^2*(rmsError n z false+rmsError n z true) +
      |((n:ℝ)+1)^2*(weight (1/2) n-weight 2 n)-π^2/40| *modeConstant := by
  let a := ((n:ℝ)+1)^2
  let d := a*(weight (1/2) n-weight 2 n)-π^2/40
  let μ := seedLaw ((n+1)^32)
  let X := score (n+1) ((n+1)^32)
  let V := discrepancy n z false-discrepancy n z true
  have hx := score_bound (m:=(n+1)^32) hn (by positivity)
  have hv : MemLp V 2 μ := (hm false).sub (hm true)
  have eq : pairedError n z = (a • V) + (d • X) := by
    funext ω
    change a*(endpoint n z false ω-endpoint n z true ω)-(π^2/40)*X ω =
      a*(discrepancy n z false ω-discrepancy n z true ω)+d*X ω
    simp only [discrepancy,endpoint,reference,benchmarkRate,Bool.false_eq_true,ite_false,ite_true,X,score,d]
    ring
  have hA : MemLp (a • V) 2 μ := hv.const_smul a
  have hD : MemLp (d • X) 2 μ := hx.1.const_smul d
  rw [rms_of_mem _ (show MemLp (pairedError n z) 2 μ by rw [eq];exact hA.add hD),eq]
  apply (lpNorm_add_le hA (by norm_num)).trans
  rw [lpNorm_const_smul,lpNorm_const_smul]
  change |a| * lpNorm V 2 μ + |d| * lpNorm X 2 μ ≤ _
  rw [abs_of_nonneg (show 0≤a by unfold a;positivity)]
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg d))
  unfold rmsError
  rw [rms_of_mem _ (hm false),rms_of_mem _ (hm true)]
  exact mul_le_mul_of_nonneg_left (lpNorm_sub_le (hm false) (by norm_num)) (sq_nonneg _)

/-- At finite N, the scaled paired error around the exact grid coefficient
costs at most the sum of the two scaled marginal RMS discrepancies. -/
theorem scaled_reference_error (n : ℕ) (_hn : 3≤n+1) (z : Family (n+1))
    (hm : ∀ q, MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32))) :
    √(∫ ω, (((n:ℝ)+1)^2*(endpoint n z false ω-endpoint n z true ω)-
       (((n:ℝ)+1)^2*(weight (1/2) n-weight 2 n))*score (n+1) ((n+1)^32) ω)^2 ∂seedLaw ((n+1)^32)) ≤
       ((n:ℝ)+1)^2*(rmsError n z false+rmsError n z true) := by
  let a := ((n:ℝ)+1)^2
  let μ := seedLaw ((n+1)^32)
  let V := discrepancy n z false-discrepancy n z true
  have eq (ω : Seed ((n+1)^32)) : a*(endpoint n z false ω-endpoint n z true ω)-
       (a*(weight (1/2) n-weight 2 n))*score (n+1) ((n+1)^32) ω = (a • V) ω := by
    change _ = a*(discrepancy n z false ω-discrepancy n z true ω)
    simp only [discrepancy,endpoint,reference,benchmarkRate,Bool.false_eq_true,ite_false,ite_true,score]
    ring
  have hv : MemLp V 2 μ := (hm false).sub (hm true)
  change √(∫ ω, (a*(endpoint n z false ω-endpoint n z true ω)-(a*(weight (1/2) n-weight 2 n))*score _ _ ω)^2 ∂μ) ≤ _
  simp_rw [eq]
  rw [rms_of_mem _ (hv.const_smul a),lpNorm_const_smul]
  change |a| * lpNorm V 2 μ ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  unfold rmsError
  rw [rms_of_mem _ (hm false),rms_of_mem _ (hm true)]
  exact mul_le_mul_of_nonneg_left (lpNorm_sub_le (hm false) (by norm_num)) (sq_nonneg _)

theorem discrepancy_mem (n : ℕ) (z : Family (n+1)) (q : Bool) (start : ∀ ω, z q ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/√(((n+1)^32:ℕ):ℝ))
      (benchmarkRate q) (horizon ((n:ℝ)+1)) (z q ω))
    (meas : Measurable (fun ω => z q ω (horizon ((n:ℝ)+1)))) :
    MemLp (discrepancy n z q) 2 (seedLaw ((n+1)^32)) := by
  have ht : 0<benchmarkRate q := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (rate_bounds q).1
  have wb := weight_bounds n ht.le
  have he := (gaussian_flow_fourth_sharp (Nat.succ_pos n) (pow_pos (Nat.succ_pos n) 32) ht (rate_bounds q).2
    (Nat.cast_nonneg (horizon ((n:ℝ)+1))) wb.1 wb.2 (z q) start flow meas).1.mono_exponent (by norm_num : (2:ENNReal) ≤ 4)
  exact he

set_option maxHeartbeats 1200000 in
/-- There is a shared-seed sequence of actual measurable global flows, over
all odd N≥33, whose scaled difference converges in RMS to the random
initial-grid statistic multiplied by π²/40. -/
theorem exists_actual_paired_coefficient :
    ∃ z : (i : ℕ) → Family (oddIndex i+1),
      (∀ i q ω, z i q ω 0=ω) ∧
      (∀ i q T, 0≤T → (∀ ω, IsFlow (circleInput (oddIndex i+1)) (circleLabel (oddIndex i+1))
        (1/sqrt (((oddIndex i+1)^32:ℕ):ℝ)) (benchmarkRate q) T (z i q ω)) ∧ Measurable (fun ω => z i q ω T)) ∧
      Tendsto (fun i => √(∫ ω, pairedError (oddIndex i) (z i) ω^2 ∂seedLaw ((oddIndex i+1)^32))) atTop (𝓝 0) := by
  have ex (i : ℕ) := exists_paired_actual_tracking (oddIndex i) (by unfold oddIndex;omega) (⟨i+16,rfl⟩)
  choose z start flows _events norms using ex
  refine ⟨z,start,flows,?_⟩
  let N (i : ℕ) := (oddIndex i:ℝ)+1
  have grow : Tendsto oddIndex atTop atTop := tendsto_atTop_mono (f:=id) (fun i => by unfold oddIndex; dsimp;omega) tendsto_id
  have H (i : ℕ) (q : Bool) : MemLp (discrepancy (oddIndex i) (z i) q) 2 (seedLaw ((oddIndex i+1)^32)) := by
    exact discrepancy_mem (oddIndex i) (z i) q (start i q) (flows i q _ (Nat.cast_nonneg _)).1 (flows i q _ (Nat.cast_nonneg _)).2
  have growth : Tendsto N atTop atTop := tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp grow)
  have D (i : ℕ) : 0<N i := by unfold N; positivity
  have lim (q : Bool) : Tendsto (fun i => N i^2*rmsError (oddIndex i) (z i) q) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => mul_nonneg (sq_nonneg _) (sqrt_nonneg _)) (g:=fun i => rmsConstant*(sqrt (N i))⁻¹)
    · intro i
      apply (mul_le_mul_of_nonneg_left (norms i q) (sq_nonneg (N i))).trans
      change N i^2*(rmsConstant/(N i^2*sqrt (N i))) ≤ _
      apply le_of_eq; field_simp [(D i).ne']
    · simpa using (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp growth)).const_mul rmsConstant
  have c := (CircleLayerRates.coefficient_limit.comp grow).sub_const (π^2/40)
  have l := ((lim false).add (lim true)).add (c.abs.mul_const modeConstant)
  apply squeeze_zero (fun _ => sqrt_nonneg _) (fun i => paired_estimate _ (by unfold oddIndex;omega) _ (H i))
  simpa [N,Function.comp_def,mul_add] using l

end CirclePairedCoefficient
