module

public import CircleMajorityFold
public import CircleGaussianCDF
import all CircleGaussianCDF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import all CircleMajorityCF
import all CircleMajorityFold
import all CircleReferenceMoments
import all CircleKernelIdentification
public import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! At a fixed odd training-grid size the Gaussian majority limit has an elementary variance. -/
public section
noncomputable section
namespace CircleMajorityLimit
open Real MeasureTheory ProbabilityTheory Filter Set CircleMajorityCF CircleMajorityFold
  CircleEscapeBridge CircleReferenceMoments CircleKernelIdentification CircleInitializationConcentration
open scoped Topology

/-- Variance of a single unit, also the variance of the normalized grid mean at positive width. -/
def fixedVariance (N : ℕ) := (CircleMajorityFold.amplitude N)^2*(1+sin (2*halfCell N)/(2*halfCell N))

private theorem gridMean_meas (N m : ℕ) : Measurable (CircleScoreMargin.gridMean N m) := by
  rw [show CircleScoreMargin.gridMean N m = fun z => (1/√(m:ℝ))*∑ j : Fin m, single N ((currySeed m z) j) from funext (gridMean_eq_sum N m)]
  unfold single gridFeature phi projection; simp only [show ∀z : Seed m, ∀j, currySeed m z j = fun k => z (j,k) by intros; rfl]; fun_prop

private theorem single_meas (N : ℕ) : Measurable (single N) := by unfold single gridFeature phi projection; fun_prop

private theorem variance_pos {N : ℕ} (hn : 3≤N) : 0<fixedVariance N := by
  have np : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have dp : 0<halfCell N := by unfold halfCell; positivity
  have ub : 2*halfCell N<π := by
    unfold halfCell; rw [←mul_div_assoc]; apply (div_lt_iff₀ (by positivity)).mpr
    have hp := mul_lt_mul_of_pos_left (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N)) pi_pos
    linarith
  have h₂ := sin_pos_of_pos_of_lt_pi (mul_pos two_pos dp) ub
  have h₁ := sin_pos_of_pos_of_lt_pi dp (by linarith)
  unfold fixedVariance CircleMajorityFold.amplitude; positivity

/-- Direct Gaussian polar integration gives the exact finite-grid variance used in the code. -/
theorem single_moments {N : ℕ} (hn : 3≤N) (ho : Odd N) :
    (∫ z, single N z ∂atomLaw)=0 ∧ (∫ z, single N z^2 ∂atomLaw)=fixedVariance N := by
  constructor
  · change (∫ z, (split z).1*gridFeature N (split z).2 ∂atomLaw)=0
    rw [split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => p.1*gridFeature N p.2),
      integral_prod_mul (fun a : ℝ => a) (gridFeature N),integral_id_gaussianReal,zero_mul]
  change (∫ z, ((split z).1*gridFeature N (split z).2)^2 ∂atomLaw)=_
  rw [split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => (p.1*gridFeature N p.2)^2)]
  simp_rw [mul_pow]
  rw [integral_prod_mul (fun a : ℝ => a^2) (fun w => gridFeature N w^2),gaussian_second,one_mul,
    standardPair_integral,gaussian_polar_separate _ (fun r : ℝ => r^2) (fun θ => (angular N θ)^2)]
  · have radial : (∫ r in Ioi (0:ℝ),r*exp (-(1/2)*r^2)*r^2)=2 := by
      convert radial_three using 1; apply integral_congr_ae; exact ae_of_all _ (fun r => by ring)
    rw [radial,mul_right_comm,angular_average hn ho (fun x => x^2) (by fun_prop)]
    simp only [mul_pow,intervalIntegral.integral_const_mul,integral_cos_sq,cos_neg,sin_neg,
      fixedVariance,sin_two_mul]
    have dp : 0<halfCell N := by unfold halfCell; positivity
    field_simp; ring
  · intro r hr θ; rw [grid_polar N hr.le,mul_pow]

/-- The actual finite-width grid score has exactly this same variance at every positive width. -/
theorem gridMean_moments {N m : ℕ} (hn : 3≤N) (ho : Odd N) (hm : 0<m) :
    (∫ z, CircleScoreMargin.gridMean N m z ∂seedLaw m)=0 ∧
      variance (CircleScoreMargin.gridMean N m) (seedLaw m) = fixedVariance N := by
  obtain ⟨zero,sq⟩ := single_moments hn ho
  have mem : MemLp (single N) 2 atomLaw := (memLp_two_iff_integrable_sq (single_meas N).aestronglyMeasurable).mpr
    (.of_integral_ne_zero (sq.trans_ne (variance_pos hn).ne'))
  have eq : CircleScoreMargin.gridMean N m = fun z => √(m:ℝ)*sampleAverage (single N) z := by
    funext z; rw [gridMean_eq_sum,sampleAverage,←mul_assoc]
    have h : 1/√(m:ℝ)=√(m:ℝ)*(m:ℝ)⁻¹ := by
      field_simp [show (m:ℝ)≠0 by exact_mod_cast hm.ne']; nlinarith [sq_sqrt (Nat.cast_nonneg m)]
    rw [h]; rfl
  rw [eq,integral_const_mul,average_mean hm mem,zero,mul_zero,variance_const_mul,
    average_variance hm mem,variance_eq_sub mem,zero,sq_sqrt (Nat.cast_nonneg m)]
  simp only [Pi.pow_apply,sq,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,sub_zero,true_and]
  field_simp

/-- Weak convergence of the actual width-indexed laws at fixed design N. -/
theorem gridMean_limit {N : ℕ} (hn : 3≤N) (ho : Odd N) :
    TendstoInDistribution (fun m => CircleScoreMargin.gridMean N m) atTop (fun x : ℝ => x)
      seedLaw (gaussianReal 0 (fixedVariance N).toNNReal) := by
  have hv := variance_pos hn
  let v := fixedVariance N
  let s := sqrt v
  have sp : 0<s := sqrt_pos.mpr hv
  have ss : s^2=v := sq_sqrt hv.le
  let X (z : Atom) := s⁻¹*single N z
  have hX : Measurable X := measurable_const.mul (single_meas N)
  obtain ⟨zero,sq⟩ := single_moments hn ho
  have init : (∫ z, X z ∂atomLaw)=0 := by simp [X,integral_const_mul,zero]
  have unit : (∫ z, X z^2 ∂atomLaw)=1 := by
    simp only [X,mul_pow,integral_const_mul,sq,inv_pow,ss]; exact inv_mul_cancel₀ hv.ne'
  refine ⟨fun m => (gridMean_meas N m).aemeasurable, aemeasurable_id, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  change Tendsto (fun m => charFun ((seedLaw m).map (CircleScoreMargin.gridMean N m)) t) _
    (𝓝 (charFun ((gaussianReal 0 v.toNNReal).map id) t))
  have limit := tendsto_charFun_inv_sqrt_mul_pow hX.aemeasurable init unit (s*t)
  convert limit using 1
  · funext m
    rw [gridMean_charFun,show X = fun z => s⁻¹*single N z from rfl,
      charFun_map_mul_comp (single_meas N).aemeasurable,single_charFun]
    rw [show s⁻¹*((√(m:ℝ))⁻¹*(s*t)) = t/√(m:ℝ) by field_simp]
  · rw [Measure.map_id,charFun_gaussianReal]
    simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
      Complex.ofReal_mul,mul_pow,←Complex.ofReal_pow,ss]
    have eq : ((v.toNNReal:NNReal):ℝ)=v := Real.coe_toNNReal _ hv.le
    rw [eq]; congr 2; ring

/-- Fixed-grid ordinary majority probability for strict thresholding of the actual grid mean. -/
theorem majority_limit {N : ℕ} (hn : 3≤N) (ho : Odd N) :
    Tendsto (fun m => (seedLaw m).real {z | CircleScoreMargin.gridMean N m z<1}) atTop
      (𝓝 ((gaussianReal 0 (fixedVariance N).toNNReal).real (Iio 1))) := by
  let μ := gaussianReal 0 (fixedVariance N).toNNReal
  have : NullSingletonClass μ := nullSingletonClass_gaussianReal (by
    exact ne_of_gt (Real.toNNReal_pos.mpr (variance_pos hn)))
  have dist := gridMean_limit hn ho
  have null : (μ.map id) (frontier (Iio (1:ℝ)))=0 := by simp
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' dist.tendsto null
  change Tendsto (fun m => ((seedLaw m).map (CircleScoreMargin.gridMean N m)) (Iio 1)) _
    (𝓝 ((μ.map id) (Iio 1))) at h
  simp_rw [Measure.map_apply (gridMean_meas _ _) measurableSet_Iio,Measure.map_id] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top μ (Iio 1))).comp h

/-- Standard-normal CDF form of the majority probability in the calculation. -/
theorem majority_normalCDF {N : ℕ} (hn : 3≤N) (ho : Odd N) :
    Tendsto (fun m => (seedLaw m).real {z | CircleScoreMargin.gridMean N m z<1}) atTop
      (𝓝 (CircleGaussianCDF.normalCDF (1/√(fixedVariance N)))) := by
  rw [←CircleGaussianCDF.scale _ _ (variance_pos hn)]
  have : NullSingletonClass (gaussianReal 0 (fixedVariance N).toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr (variance_pos hn)))
  simpa only [CircleGaussianCDF.varianceCDF,Measure.real,measure_congr Iio_ae_eq_Iic] using majority_limit hn ho

/-- Large-grid limit of the explicit fixed-grid variance. -/
theorem variance_limit : Tendsto fixedVariance atTop (𝓝 (2/π^2)) := by
  have z : Tendsto halfCell atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (π/2)
    change Tendsto (fun N : ℕ => π/(2*(N:ℝ))) _ _
    simpa [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h
  have q := continuous_sinc.continuousAt.tendsto.comp z
  have q' := continuous_sinc.continuousAt.tendsto.comp (z.const_mul 2)
  have q1 : Tendsto (fun N => sinc (halfCell N)) atTop (𝓝 1) := by simpa [Function.comp_def] using q
  have q2 : Tendsto (fun N => sinc (2*halfCell N)) atTop (𝓝 1) := by simpa [Function.comp_def] using q'
  have h := ((tendsto_const_nhds (x:=(1:ℝ))).div (q1.const_mul π) (by simp)).pow 2
  have result := h.mul ((tendsto_const_nhds (x:=(1:ℝ))).add q2)
  convert result.congr' _ using 1
  · congr 1; ring
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have n : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have d : 0<halfCell N := by unfold halfCell; positivity
    change (1/(π*sinc (halfCell N)))^2*(1+sinc (2*halfCell N))=fixedVariance N
    rw [sinc_of_ne_zero d.ne',sinc_of_ne_zero (mul_pos two_pos d).ne',fixedVariance,
      CircleMajorityFold.amplitude]
    congr 3
    dsimp [halfCell]; field_simp

/-- Taking the grid limit after the fixed-grid width limit gives Φ(π/√2). -/
theorem majority_continuum : Tendsto (fun N => CircleGaussianCDF.normalCDF (1/√(fixedVariance N))) atTop
    (𝓝 (CircleGaussianCDF.normalCDF (π/√2))) := by
  have v : 0<(2/π^2) := by positivity
  have lim := (tendsto_const_nhds (x:=(1:ℝ))).div variance_limit.sqrt (sqrt_pos.mpr v).ne'
  have eq : 1/√(2/π^2)=π/√2 := by rw [sqrt_div (by norm_num),sqrt_sq pi_pos.le]; field_simp
  rw [←eq]
  exact (CircleGaussianCDF.normalCDF_deriv _).continuousAt.tendsto.comp lim

end CircleMajorityLimit
