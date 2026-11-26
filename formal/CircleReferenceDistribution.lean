module
public import CircleReferenceMixture
public import CircleReferenceKurtosis
public import CircleGaussianCDF
public import CircleDynamics
import all CircleReferenceMixture
import all CircleGaussianCDF
import all CircleReferenceMoments
import all CircleReferenceKurtosis
import all CircleSpectrum
import all CircleInitializationConcentration
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Gaussian comparison for the finite-width reference under the benchmark's
original seed law. The bound uses cancellation of the first variation in
the conditional variance. -/
public section
noncomputable section
namespace CircleReferenceDistribution
open ProbabilityTheory MeasureTheory Real Set CircleEscapeBridge CircleInitializationConcentration
  CircleReferenceMixture CircleGaussianCDF
open scoped ENNReal

def featureVariance (N : ℕ) (b : ℝ) := ∫ z, squaredFeature N b z ∂atomLaw

theorem featureVariance_eq {n : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) :
    featureVariance (n+1) b=CircleSpectrum.c0*(1-b)^2+b^2*CircleSpectrum.S n := CircleReferenceKurtosis.mean_squaredFeature n hn ho b

theorem featureVariance_pos {n : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (b : ℝ) :
    0<featureVariance (n+1) b := by
  have hf : 0<CircleSpectrum.S n := lt_of_lt_of_le (by positivity) (CircleReferenceKurtosis.S_lower n)
  rw [featureVariance_eq hn ho b]
  by_cases h : b=0
  · simp [h,CircleSpectrum.c0,pi_pos]
  · exact add_pos_of_nonneg_of_pos (by unfold CircleSpectrum.c0;positivity) (mul_pos (sq_pos_of_ne_zero h) hf)

private theorem mixing_meas (N m : ℕ) (b : ℝ) : Measurable (mixingVariance N m b) :=
  Finset.measurable_fun_sum _ fun j _ => (CircleReferenceMixture.loading_meas N m b j).pow_const _

private theorem nonneg (N m : ℕ) (b : ℝ) (h : Hidden m) : 0≤mixingVariance N m b h :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Real-valued CDF equality for the conditional variance, integrated on
the original seed space. -/
theorem cdf_mixture (N m : ℕ) (hm : 0<m) (b x : ℝ) :
    (seedLaw m).real {ω | reference N m b ω-b ≤ x} =
      ∫ ω, varianceCDF (mixingVariance N m b (splitLayer m ω).2) x ∂seedLaw m := by
  let f (h : Hidden m) := varianceCDF (mixingVariance N m b h) x
  have hf : Measurable f := (varianceCDF_measurable x).comp (mixing_meas N m b)
  have hs : MeasurePreserving (fun ω => (splitLayer m ω).2) (seedLaw m) (hiddenLaw m) :=
    measurePreserving_snd.comp (CircleInitializationConcentration.split_preserving m)
  change _ = ∫ ω, (f ∘ (fun a => (splitLayer m a).2)) ω ∂seedLaw m
  rw [hs.hasLaw.integral_comp hf.aestronglyMeasurable]
  have he (h : Hidden m) : ENNReal.ofReal (f h)=gaussianReal 0 (mixingVariance N m b h).toNNReal (Iic x) :=
    ofReal_measureReal
  have hk := mixture N m hm b (A:=Iic x) measurableSet_Iic
  change ((seedLaw m) {ω | reference N m b ω-b ∈ Iic x}).toReal = _
  rw [hk,← funext he]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
    hf.aestronglyMeasurable).symm

/-- A centered, unit-mean random variance with finite second moment only
changes the standard Gaussian CDF in second order. -/
theorem mixture_kolmogorov {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω→ℝ} (hS : MemLp S 2 μ) (hs : ∀ ω, 0≤S ω) (mean : ∫ ω, S ω ∂μ=1) (t : ℝ) :
    |(∫ ω, varianceCDF (S ω) t ∂μ)-normalCDF t| ≤ 5*variance S μ := by
  have hc : Integrable (fun ω => varianceCDF (S ω) t) μ :=
    Integrable.of_bound ((varianceCDF_measurable t).comp_aemeasurable hS.aemeasurable).aestronglyMeasurable 1
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤varianceCDF (S ω) t from measureReal_nonneg)];exact measureReal_le_one))
  have hlin : Integrable (fun ω => S ω-1) μ := (hS.integrable (by norm_num)).sub (integrable_const 1)
  have hmain : Integrable (fun ω => varianceCDF (S ω) t-normalCDF t) μ := hc.sub (integrable_const _)
  have hsquare := (hS.sub (memLp_const (1:ℝ))).integrable_sq
  let R ω := varianceCDF (S ω) t-normalCDF t-slope t*(S ω-1)
  have sqi : Integrable (fun ω => 5*(S ω-1)^2) μ := hsquare.const_mul 5
  have hr : |(∫ ω, R ω ∂μ)| ≤ ∫ ω, 5*(S ω-1)^2 ∂μ := by
    rw [←Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (f:=R) sqi (ae_of_all _ fun ω => tangent_remainder _ _ (hs ω))
  have hi : (∫ ω, R ω ∂μ)=(∫ ω, varianceCDF (S ω) t ∂μ)-normalCDF t := by
    unfold R
    rw [integral_sub hmain (hlin.const_mul _),
      integral_sub hc (integrable_const _),integral_const_mul,integral_sub (hS.integrable (by norm_num)) (integrable_const _),mean]
    simp
  rw [hi,integral_const_mul] at hr
  simpa only [variance_eq_integral hS.aemeasurable,mean] using hr

/-- At every width, all thresholds have Kolmogorov error at most five times
the relative single-neuron variance divided by width. -/
theorem reference_kolmogorov (N m : ℕ) (hm : 0<m) (b : ℝ) (hv : 0<featureVariance N b) (t : ℝ) :
    |(seedLaw m).real {ω | (reference N m b ω-b)/√(featureVariance N b) ≤ t}-normalCDF t|
      ≤ 5*variance (squaredFeature N b) atomLaw/(m*(featureVariance N b)^2) := by
  let V := featureVariance N b
  let S ω := sampleAverage (m:=m) (squaredFeature N b) ω / V
  have hv' : 0<V := hv
  have hx := CircleReferenceMixture.squared_mem N b
  have hS : MemLp S 2 (seedLaw m) := by simpa only [S,div_eq_mul_inv] using (average_mem (m:=m) hx).mul_const V⁻¹
  have hmS : ∫ ω, S ω ∂seedLaw m=1 := by
    unfold S
    rw [integral_div,average_mean hm hx]
    exact div_self hv'.ne'
  have hp (ω : Seed m) : 0≤S ω := by
    unfold S
    rw [←variance_as_average _ _ hm b]
    exact div_nonneg (nonneg _ _ _ _) hv'.le
  have hk := mixture_kolmogorov hS hp hmS t
  have hsc : (fun ω => varianceCDF (S ω) t) = fun ω => varianceCDF (mixingVariance N m b (splitLayer m ω).2) (t*√V) := by
    ext ω
    rw [rescale _ _ _ (nonneg _ _ _ _) hv',variance_as_average _ _ hm b]
  have hset : {ω | (reference N m b ω-b)/√(featureVariance N b) ≤ t} = {ω | reference N m b ω-b ≤ t*√V} :=
    Set.ext fun _ => div_le_iff₀ (sqrt_pos.mpr hv')
  have hvar : variance S (seedLaw m)=variance (squaredFeature N b) atomLaw / (m*V^2) := by
    simp only [S,div_eq_mul_inv,variance_mul_const,average_variance hm hx]
    ring
  rw [hset,cdf_mixture N m hm b,←hsc]
  rw [hvar] at hk
  simpa only [V,mul_div_assoc] using hk

/-- The same-seed output inherits the Gaussian comparison from a coupling
with physical error at most e except on a set of probability δ. -/
theorem training_kolmogorov (N m : ℕ) (hm : 0<m) (b : ℝ) (hv : 0<featureVariance N b)
    (Y : Seed m→ℝ) {e δ : ℝ} (he : 0≤e)
    (failure : (seedLaw m).real {ω | e < |Y ω-reference N m b ω|} ≤ δ) (t : ℝ) :
    |(seedLaw m).real {ω | (Y ω-b)/√(featureVariance N b) ≤ t}-normalCDF t| ≤
      5*variance (squaredFeature N b) atomLaw/(m*(featureVariance N b)^2)+δ+
        e/√(2*π*featureVariance N b) := by
  let V := featureVariance N b
  have hs : 0<√V := sqrt_pos.mpr hv
  have hF : (seedLaw m).real {ω | e/√V < |(Y ω-b)/√V-(reference N m b ω-b)/√V|} ≤ δ := by
    convert failure using 3
    ext ω
    rw [←sub_div,sub_sub_sub_cancel_right,abs_div,abs_of_pos hs,div_lt_div_iff_of_pos_right hs]
  have h := CircleDynamics.kolmogorov_transfer (seedLaw m) (fun ω => (Y ω-b)/√V)
    (fun ω => (reference N m b ω-b)/√V) normalCDF (e/√V) δ _ _ (div_nonneg he hs.le)
    hF (reference_kolmogorov _ _ hm b hv) normalCDF_lipschitz t
  rw [sqrt_mul (show 0≤2*π by positivity)]
  convert h using 1
  dsimp [V]
  ring

private theorem ratio_bound (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) (b : ℝ) :
    5*variance (squaredFeature (n+1) b) atomLaw/(m*(featureVariance (n+1) b)^2)
      ≤ 5*CircleReferenceKurtosis.ratioConstant/m := by
  have hv := featureVariance_pos hn ho b
  apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hm) (sq_pos_of_pos hv))).mpr
  have h := mul_le_mul_of_nonneg_left (CircleReferenceKurtosis.relative_variance n hn ho b) (by norm_num : (0:ℝ)≤5)
  refine h.trans_eq ?_
  change 5*(CircleReferenceKurtosis.ratioConstant*(featureVariance (n+1) b)^2)=_
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

/-- The constant is uniform over every odd grid, positive width, threshold,
and real interpolation weight. -/
theorem uniform_kolmogorov (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) (b t : ℝ) :
    |(seedLaw m).real {ω | (reference (n+1) m b ω-b)/√(featureVariance (n+1) b) ≤ t}-normalCDF t|
      ≤ 5*CircleReferenceKurtosis.ratioConstant/m := by
  exact (reference_kolmogorov _ _ hm b (featureVariance_pos hn ho b) t).trans (ratio_bound n m hn ho hm b)

theorem uniform_training (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m)
    (b : ℝ) (Y : Seed m→ℝ) {e δ : ℝ} (he : 0≤e)
    (failure : (seedLaw m).real {ω | e < |Y ω-reference (n+1) m b ω|} ≤ δ) (t : ℝ) :
    |(seedLaw m).real {ω | (Y ω-b)/√(featureVariance (n+1) b) ≤ t}-normalCDF t| ≤
      5*CircleReferenceKurtosis.ratioConstant/m+δ+e/√(2*π*featureVariance (n+1) b) := by
  refine (training_kolmogorov _ _ hm b (featureVariance_pos hn ho b) Y he failure t).trans ?_
  linarith only [ratio_bound n m hn ho hm b]

end CircleReferenceDistribution
