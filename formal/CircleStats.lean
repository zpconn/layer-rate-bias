module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic

/-!
# Variance of an interpolated statistic and a teacher certificate

All laws are conditional on the fixed design. The covariance normal equations are
stated as finite sums, so any solution can be used even if the Gram matrix is singular.
-/
public section

namespace CircleStats

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

noncomputable def weighted (X : ι → Ω → ℝ) (p : ι → ℝ) : Ω → ℝ := ∑ i, p i • X i

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ι → Ω → ℝ} {q : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
private theorem weighted_mem (hX : ∀ i, MemLp (X i) 2 μ) (p : ι → ℝ) :
    MemLp (weighted X p) 2 μ :=
  memLp_finsetSum' _ fun i _ ↦ (hX i).const_smul (p i)

private theorem cov_weighted (hX : ∀ i, MemLp (X i) 2 μ) (hq : MemLp q 2 μ) (p : ι → ℝ) :
    covariance (weighted X p) q μ = ∑ i, p i * covariance (X i) q μ := by
  rw [weighted, covariance_sum_left (fun i ↦ (hX i).const_smul (p i)) hq]
  simp only [covariance_smul_left]

/-- Seed variance splits into optimal residual variance and a nonnegative excess.
The final variance is the Gram quadratic form for the weight discrepancy. -/
theorem variance_decomposition (hX : ∀ i, MemLp (X i) 2 μ) (hq : MemLp q 2 μ)
    (w p : ι → ℝ) (labelTerm : ℝ)
    (normal : ∀ i, ∑ j, w j * covariance (X j) (X i) μ = covariance q (X i) μ) :
    variance (fun ω ↦ (q - weighted X p) ω + labelTerm) μ =
      (variance q μ - ∑ i, w i * covariance (X i) q μ) +
        variance (weighted X p - weighted X w) μ := by
  have horth (u : ι → ℝ) : covariance (weighted X w) (weighted X u) μ =
      covariance q (weighted X u) μ := by
    rw [covariance_comm (X := weighted X w), cov_weighted hX (weighted_mem hX w),
      covariance_comm (X := q), cov_weighted hX hq]
    apply Finset.sum_congr rfl
    intro i _
    rw [covariance_comm (X := X i), cov_weighted hX (hX i), normal,
      covariance_comm (X := q)]
  have hw := horth w
  rw [covariance_self (weighted_mem hX w).aemeasurable, covariance_comm (X := q),
    cov_weighted hX hq] at hw
  rw [variance_add_const (hq.sub (weighted_mem hX p)).aestronglyMeasurable,
    variance_sub hq (weighted_mem hX p), variance_sub (weighted_mem hX p) (weighted_mem hX w),
    covariance_comm (X := weighted X p), horth, hw]
  ring

/-- The excess variance above is exactly the usual double Gram sum. -/
theorem gram_variance (hX : ∀ i, MemLp (X i) 2 μ) (u : ι → ℝ) :
    variance (weighted X u) μ =
      ∑ i, ∑ j, u i * (u j * covariance (X i) (X j) μ) := by
  rw [weighted, variance_sum (fun i ↦ (hX i).const_smul (u i))]
  simp only [covariance_smul_left, covariance_smul_right, mul_left_comm]

omit [MeasurableSpace Ω] in
theorem weighted_sub (p w : ι → ℝ) :
    weighted X p - weighted X w = weighted X (p - w) := by
  simp only [weighted, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- For centered initial statistics the deterministic label term is exactly the seed mean. -/
theorem statistic_mean (hX : ∀ i, MemLp (X i) 2 μ) (hq : MemLp q 2 μ)
    (centerX : ∀ i, ∫ ω, X i ω ∂μ = 0) (centerQ : ∫ ω, q ω ∂μ = 0)
    (p : ι → ℝ) (labelTerm : ℝ) :
    ∫ ω, ((q - weighted X p) ω + labelTerm) ∂μ = labelTerm := by
  rw [integral_add ((hq.sub (weighted_mem hX p)).integrable one_le_two) (integrable_const _)]
  simp only [Pi.sub_apply]
  rw [integral_sub (hq.integrable one_le_two) ((weighted_mem hX p).integrable one_le_two), centerQ]
  simp only [weighted, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum]
  · simp [integral_const_mul, centerX]
  · exact fun i _ ↦ ((hX i).integrable one_le_two).const_mul _

/-- Squared error about a known target equals seed variance plus squared common bias. -/
theorem mse_decomposition {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) (target : ℝ) :
    ∫ ω, (Z ω - target)^2 ∂μ = variance Z μ + ((∫ ω, Z ω ∂μ) - target)^2 := by
  let D := fun ω ↦ Z ω - target
  have hd : MemLp D 2 μ := hZ.sub (memLp_const target)
  have m := variance_eq_sub hd
  change variance (fun ω ↦ Z ω - target) μ =
    (∫ ω, (Z ω - target)^2 ∂μ) - (∫ ω, Z ω - target ∂μ)^2 at m
  rw [variance_sub_const hZ.aestronglyMeasurable, integral_sub (hZ.integrable one_le_two)
    (integrable_const _)] at m
  simp only [integral_const, probReal_univ, one_smul] at m
  linarith

omit [IsProbabilityMeasure μ] in
private theorem norm_toLp_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ ω, f ω^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, Real.norm_eq_abs]

/-- On a common seed space, an L² comparison of predictions controls the
difference between their standard deviations with constant one. -/
theorem sd_transfer {Y Z : Ω → ℝ} (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    |Real.sqrt (variance Y μ) - Real.sqrt (variance Z μ)| ≤
      Real.sqrt (∫ ω, (Y ω - Z ω)^2 ∂μ) := by
  let C (f : Ω → ℝ) := fun ω ↦ f ω - ∫ u, f u ∂μ
  have hc {f : Ω → ℝ} (hf : MemLp f 2 μ) : MemLp (C f) 2 μ := hf.sub (memLp_const _)
  have hsd {f : Ω → ℝ} (hf : MemLp f 2 μ) :
      Real.sqrt (variance f μ) = ‖(hc hf).toLp (C f)‖ := by
    rw [variance_eq_integral hf.aemeasurable]
    change Real.sqrt (∫ ω, C f ω^2 ∂μ) = _
    rw [← norm_toLp_sq (hc hf), Real.sqrt_sq (norm_nonneg _)]
  have hd : C Y - C Z = C (Y - Z) := by
    ext ω
    simp only [C, Pi.sub_apply, integral_sub (hY.integrable one_le_two) (hZ.integrable one_le_two)]
    ring
  have hdiff : ‖(hc hY).toLp (C Y) - (hc hZ).toLp (C Z)‖ =
      Real.sqrt (variance (Y - Z) μ) := by
    rw [← MemLp.toLp_sub, hsd (hY.sub hZ)]
    congr 1
    apply Lp.ext
    filter_upwards [(hc hY |>.sub (hc hZ)).coeFn_toLp, (hc (hY.sub hZ)).coeFn_toLp]
      with ω h₁ h₂
    rw [h₁, h₂]
    exact congrFun hd ω
  rw [hsd hY, hsd hZ]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [hdiff]
  exact Real.sqrt_le_sqrt (variance_le_expectation_sq (hY.sub hZ).aestronglyMeasurable)

section Gaussian

/-- The sigma-algebra generated by the observed vector. -/
abbrev sampleSigma (X : ι → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance

/-- Under joint Gaussianity the normal-equation residual is independent of all
sampled values jointly. No invertibility assumption is needed once a solve is given. -/
theorem gaussian_residual_independent
    (gauss : HasGaussianLaw (fun ω ↦ (q ω, fun i ↦ X i ω)) μ) (w : ι → ℝ)
    (normal : ∀ i, ∑ j, w j * covariance (X j) (X i) μ = covariance q (X i) μ) :
    IndepFun (q - weighted X w) (fun ω i ↦ X i ω) μ := by
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ i, w i • ContinuousLinearMap.proj i
  let P := ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)
  let F := ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)
  let residualMap := F - L.comp P
  let transform := (ContinuousLinearMap.pi (fun _ : Unit ↦ residualMap)).prod P
  have hg : HasGaussianLaw (fun ω ↦ (fun _ : Unit ↦ (q - weighted X w) ω,
      fun i ↦ X i ω)) μ := by
    convert gauss.map_fun transform using 1
    funext ω
    ext <;> simp [transform, residualMap, F, P, L, weighted, smul_eq_mul]
  have hi := hg.indepFun_of_covariance_eval
  have hX (i : ι) : MemLp (X i) 2 μ := (gauss.snd.eval i).memLp_two
  have hind : IndepFun (fun ω (_ : Unit) ↦ (q - weighted X w) ω) (fun ω i ↦ X i ω) μ := by
    apply hi
    intro _ i
    rw [covariance_sub_left gauss.fst.memLp_two (weighted_mem hX w) (hX i),
      cov_weighted hX (hX i), normal, sub_self]
  exact hind.comp (measurable_pi_apply ()) measurable_id

/-- The conditional variance of the population statistic given its sampled values is
the constant minimum linear prediction variance in the jointly Gaussian model. -/
theorem gaussian_conditional_variance
    (gauss : HasGaussianLaw (fun ω ↦ (q ω, fun i ↦ X i ω)) μ)
    (mq : Measurable q) (mx : ∀ i, Measurable (X i)) (w : ι → ℝ)
    (normal : ∀ i, ∑ j, w j * covariance (X j) (X i) μ = covariance q (X i) μ) :
    condVar (sampleSigma X) q μ =ᵐ[μ] fun _ ↦ variance q μ - ∑ i, w i * covariance (X i) q μ := by
  let W := weighted X w
  let R := q - W
  have hX (i : ι) : MemLp (X i) 2 μ := (gauss.snd.eval i).memLp_two
  have hW : MemLp W 2 μ := weighted_mem hX w
  have hR : MemLp R 2 μ := gauss.fst.memLp_two.sub hW
  have hind := gaussian_residual_independent gauss w normal
  have hm : (sampleSigma X) ≤ ‹MeasurableSpace Ω› := (measurable_pi_iff.mpr mx).comap_le
  have mW : Measurable[(sampleSigma X)] W := by
    have hdata : Measurable[(sampleSigma X)] (fun ω i ↦ X i ω) := Measurable.of_comap_le le_rfl
    have hwfun : W = fun x ↦ ∑ i, w i • X i x := by ext; simp [W, weighted]
    rw [hwfun]
    exact
      (show Measurable (fun v : ι → ℝ ↦ ∑ i, w i • v i) by fun_prop).comp hdata
  have mR : Measurable R := mq.sub (mW.mono hm le_rfl)
  have hR' : (MeasurableSpace.comap R inferInstance) ≤ ‹MeasurableSpace Ω› := mR.comap_le
  have measR : Measurable[MeasurableSpace.comap R inferInstance] R := Measurable.of_comap_le le_rfl
  have heR := condExp_indep_eq hR' hm measR.stronglyMeasurable hind
  have heW := condExp_of_stronglyMeasurable (μ := μ) hm mW.stronglyMeasurable
    (hW.integrable one_le_two)
  have hqrep : R + W = q := sub_add_cancel _ _
  have hcond := condExp_add (hR.integrable one_le_two) (hW.integrable one_le_two) (sampleSigma X)
  rw [hqrep, heW] at hcond
  have he2 : μ[(q - μ[q | (sampleSigma X)]) ^ 2 | (sampleSigma X)] =ᵐ[μ]
      μ[(fun ω ↦ (R ω - ∫ x, R x ∂μ)^2) | (sampleSigma X)] := by
    apply condExp_congr_ae
    filter_upwards [hcond, heR] with ω hc hr
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at hc ⊢
    rw [hc, hr]
    change (q ω - ((∫ x, R x ∂μ) + W ω))^2 = (q ω - W ω - (∫ x, R x ∂μ))^2
    ring
  have hs := condExp_indep_eq hR' hm
    ((measR.sub_const (∫ x, R x ∂μ)).pow_const 2).stronglyMeasurable hind
  have hvar : variance R μ = variance q μ - ∑ i, w i * covariance (X i) q μ := by
    have hd := variance_decomposition hX gauss.fst.memLp_two w w 0 normal
    change variance (fun ω ↦ q ω - weighted X w ω) μ = _
    simpa using hd
  refine he2.trans (hs.trans ?_)
  rw [← variance_eq_integral mR.aemeasurable, hvar]

end Gaussian

section Reference

/-- Population and grid-average covariance suffice for the finite-width reference
variance. Each square-integrable pair can be non-Gaussian. -/
theorem circle_reference_variance {Q G : Ω → ℝ} (hQ : MemLp Q 2 μ) (hG : MemLp G 2 μ)
    (c S b : ℝ) (vQ : variance Q μ = c) (vG : variance G μ = c + S)
    (cg : covariance Q G μ = c) :
    variance (fun ω ↦ Q ω - b * (G ω - 1)) μ = c * (1-b)^2 + b^2 * S := by
  have hGsub : MemLp (fun ω ↦ G ω - 1) 2 μ := hG.sub (memLp_const 1)
  rw [variance_fun_sub hQ (hGsub.const_mul b), variance_const_mul, covariance_const_mul_right,
    variance_sub_const hG.aestronglyMeasurable, covariance_sub_const_right (hG.integrable one_le_two),
    vQ, vG, cg]
  ring

/-- Normalized sums of independent neuron contributions inherit the variance of a
single contribution at every positive finite width. -/
theorem normalized_sum_variance {m : ℕ} (hm : 0 < m) (U : Fin m → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 μ) (ind : ∀ i j, i ≠ j → U i ⟂ᵢ[μ] U j)
    (v b : ℝ) (varU : ∀ i, variance (U i) μ = v) :
    variance (fun ω ↦ (Real.sqrt m)⁻¹ * (∑ i, U i) ω + b) μ = v := by
  have hsum := memLp_finsetSum' Finset.univ (fun (i : Fin m) _ ↦ hU i)
  rw [variance_add_const (hsum.const_mul _).aestronglyMeasurable,
    variance_const_mul, IndepFun.variance_sum (fun i _ ↦ hU i)
      (fun i _ j _ hij ↦ ind i j hij)]
  simp only [varU, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

/-- Optimal scalar grid-average weight, and the exact excess incurred by weight b. -/
theorem grid_variance_square (c S b : ℝ) (h : 0 < c + S) :
    c*(1-b)^2 + b^2*S =
      c*S/(c+S) + (c+S)*(b-c/(c+S))^2 := by
  field_simp [ne_of_gt h]
  ring

end Reference

section Certificate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A representer for the observable and one for each noiseless sample give a
deterministic bound for a teacher in a norm ball. `value` is the trained statistic. -/
theorem teacher_certificate (q h : E) (a : ι → E) (w y : ι → ℝ) (value R : ℝ)
    (labels : ∀ i, ⟪h, a i⟫_ℝ = y i) (radius : ‖h‖ ≤ R) :
    |value - ⟪h, q⟫_ℝ| ≤ |value - ∑ i, w i * y i| + R * ‖q - ∑ i, w i • a i‖ := by
  have hinner : ⟪h, q - ∑ i, w i • a i⟫_ℝ = ⟪h, q⟫_ℝ - ∑ i, w i * y i := by
    simp [inner_sub_right, inner_sum, real_inner_smul_right, labels]
  have hCS := (abs_real_inner_le_norm h (q - ∑ i, w i • a i)).trans
    (mul_le_mul_of_nonneg_right radius (norm_nonneg _))
  rw [hinner, abs_sub_comm] at hCS
  exact (abs_sub_le _ (∑ i, w i * y i) _).trans (add_le_add le_rfl hCS)

/-- The norm in the certificate is exactly the power function at the covariance
weights. The Gram identity is obtained directly from the normal equations. -/
theorem power_squared (q : E) (a : ι → E) (w : ι → ℝ)
    (normal : ∀ i, ∑ j, w j * ⟪a j, a i⟫_ℝ = ⟪q, a i⟫_ℝ) :
    ‖q - ∑ i, w i • a i‖ ^ 2 = ‖q‖ ^ 2 - ∑ i, w i * ⟪q, a i⟫_ℝ := by
  let z := ∑ i, w i • a i
  have normal' (i : ι) : ⟪z, a i⟫_ℝ = ⟪q, a i⟫_ℝ := by
    simpa only [z, sum_inner, real_inner_smul_left] using normal i
  have hz : ⟪z, z⟫_ℝ = ⟪q, z⟫_ℝ := by
    change ⟪z, ∑ i, w i • a i⟫_ℝ = ⟪q, ∑ i, w i • a i⟫_ℝ
    simp only [inner_sum, real_inner_smul_right, normal']
  change ‖q - z‖ ^ 2 = _
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq z, hz]
  simp only [z, inner_sum, real_inner_smul_right]
  ring

/-- Fitting the labels consumes part of the teacher's squared norm budget. The
remaining radius gives a tighter interval from the same noiseless observations. -/
theorem certificate_after_labels (q h : E) (a : ι → E) (w t y : ι → ℝ) (value R : ℝ)
    (labels : ∀ i, ⟪h, a i⟫_ℝ = y i) (radius : ‖h‖ ≤ R)
    (normal : ∀ i, ∑ j, w j * ⟪a j, a i⟫_ℝ = ⟪q, a i⟫_ℝ)
    (fit : ∀ i, ∑ j, t j * ⟪a j, a i⟫_ℝ = y i) :
    |value - ⟪h, q⟫_ℝ| ≤ |value - ∑ i, w i * y i| +
      Real.sqrt (R^2 - ∑ i, t i * y i) * ‖q - ∑ i, w i • a i‖ := by
  let h₀ := ∑ i, t i • a i
  let d := q - ∑ i, w i • a i
  have hpow : ‖h-h₀‖^2 = ‖h‖^2 - ∑ i, t i * y i := by
    simpa only [labels, h₀] using power_squared h a t (fun i ↦ (fit i).trans (labels i).symm)
  have remRad : ‖h-h₀‖ ≤ Real.sqrt (R^2 - ∑ i, t i * y i) := by
    apply Real.le_sqrt_of_sq_le
    rw [hpow]
    exact sub_le_sub_right (pow_le_pow_left₀ (norm_nonneg _) radius 2) _
  have orth (i : ι) : ⟪a i, d⟫_ℝ = 0 := by
    rw [real_inner_comm, show d = q - ∑ i, w i • a i from rfl, inner_sub_left]
    simp only [sum_inner, real_inner_smul_left, normal, sub_self]
  have hinner : ⟪h - h₀, d⟫_ℝ = ⟪h, q⟫_ℝ - ∑ i, w i * y i := by
    rw [inner_sub_left]
    have hz : ⟪h₀, d⟫_ℝ = 0 := by simp only [h₀, sum_inner, real_inner_smul_left, orth,
      mul_zero, Finset.sum_const_zero]
    simp only [hz, sub_zero, d, inner_sub_right, inner_sum, real_inner_smul_right, labels]
  have hCS := (abs_real_inner_le_norm (h - h₀) d).trans
    (mul_le_mul_of_nonneg_right remRad (norm_nonneg _))
  rw [hinner, abs_sub_comm] at hCS
  exact (abs_sub_le _ (∑ i, w i * y i) _).trans (add_le_add le_rfl hCS)

/-- Every point in the noiseless certificate interval is attained in the RKHS ball.
The parameter `s` is in [-1,1], including the two endpoints. -/
theorem certificate_attained (q : E) (a : ι → E) (w t y : ι → ℝ) (R s : ℝ)
    (hR : 0 ≤ R) (hs : |s| ≤ 1)
    (normal : ∀ i, ∑ j, w j * ⟪a j, a i⟫_ℝ = ⟪q, a i⟫_ℝ)
    (fit : ∀ i, ∑ j, t j * ⟪a j, a i⟫_ℝ = y i)
    (feasible : ∑ i, t i * y i ≤ R^2) :
    ∃ h : E, ‖h‖ ≤ R ∧ (∀ i, ⟪h, a i⟫_ℝ = y i) ∧
      ⟪h, q⟫_ℝ = ∑ i, w i * y i +
        s * Real.sqrt (R^2 - ∑ i, t i * y i) * ‖q - ∑ i, w i • a i‖ := by
  let h₀ := ∑ i, t i • a i
  let q₀ := ∑ i, w i • a i
  let d := q - q₀
  let B := Real.sqrt (R^2 - ∑ i, t i * y i)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B^2 = R^2 - ∑ i, t i * y i := Real.sq_sqrt (sub_nonneg.mpr feasible)
  have hlabel (i : ι) : ⟪h₀, a i⟫_ℝ = y i := by simpa [h₀, sum_inner, real_inner_smul_left] using fit i
  have henergy : ‖h₀‖^2 = ∑ i, t i * y i := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪h₀, ∑ i, t i • a i⟫_ℝ = _
    simp only [inner_sum, real_inner_smul_right, hlabel]
  have orth (i : ι) : ⟪d, a i⟫_ℝ = 0 := by
    simp [d, q₀, inner_sub_left, sum_inner, real_inner_smul_left, normal]
  have orth_comb (u : ι → ℝ) : ⟪d, ∑ i, u i • a i⟫_ℝ = 0 := by
    simp [inner_sum, real_inner_smul_right, orth]
  have orth₀ : ⟪h₀, d⟫_ℝ = 0 := by rw [real_inner_comm]; exact orth_comb t
  have qrep : q = d + q₀ := (sub_add_cancel _ _).symm
  have center : ⟪h₀, q⟫_ℝ = ∑ i, w i * y i := by
    calc
      _ = ⟪h₀, d + q₀⟫_ℝ := congrArg _ qrep
      _ = _ := by simp only [inner_add_right, orth₀, zero_add, q₀, inner_sum, real_inner_smul_right, hlabel]
  by_cases hzero : ‖d‖ = 0
  · refine ⟨h₀, ?_, hlabel, ?_⟩
    · nlinarith [norm_nonneg h₀]
    · change _ = _ + s*B*‖d‖
      simp [hzero, center]
  let k := s * B / ‖d‖
  have kscale : k * ‖d‖ = s * B := div_mul_cancel₀ _ hzero
  have knr : ‖k • d‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs, ← abs_of_nonneg (norm_nonneg d), ← abs_mul]
    simp only [kscale, abs_mul, abs_of_nonneg hB]
    simpa using mul_le_mul_of_nonneg_right hs hB
  refine ⟨h₀ + k • d, ?_, ?_, ?_⟩
  · have hen : ‖h₀ + k • d‖ ^ 2 = ‖h₀‖^2 + ‖k • d‖^2 := by
      simp only [norm_add_sq_real, real_inner_smul_right, orth₀, mul_zero, add_zero]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) knr 2, norm_nonneg (h₀ + k • d)]
  · intro i
    simp only [inner_add_left, real_inner_smul_left, orth, mul_zero, add_zero, hlabel]
  · have obs : ⟪d, q⟫_ℝ = ‖d‖^2 := by
      calc
        _ = ⟪d, d + q₀⟫_ℝ := congrArg _ qrep
        _ = _ := by rw [inner_add_right, orth_comb w, add_zero, real_inner_self_eq_norm_sq]
    rw [inner_add_left, center, real_inner_smul_left, obs, sq, ← mul_assoc, kscale]

end Certificate

end CircleStats
