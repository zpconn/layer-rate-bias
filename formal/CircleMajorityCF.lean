module

public import CircleScoreMargin
import all CircleScoreMargin
import all CircleFlowPath
public import CircleReferenceMoments
import all CircleReferenceMoments
import all CircleKernelIdentification
import all CircleInitializationConcentration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Exact finite-grid, finite-width characteristic function of the initial grid mean. -/
public section
noncomputable section
namespace CircleMajorityCF
open Real MeasureTheory ProbabilityTheory Set CircleInitializationConcentration CircleEscapeBridge
  CircleReferenceMoments CircleKernelIdentification CircleGridSpectrum

/-- Angular average of a single unit-length hidden feature over the training grid. -/
def angular (N : ℕ) (θ : ℝ) :=
  (∑ i : Fin N, max (cos (θ-physicalAngle i)) 0)/(N:ℝ)

private theorem angular_cont (N : ℕ) : Continuous (angular N) := by unfold angular; fun_prop

/-- The contribution before the width normalization. -/
def single (N : ℕ) (z : Atom) := z 0 * gridFeature N (z 1,z 2)

private theorem grid_polar (N : ℕ) {r : ℝ} (hr : 0≤r) (θ : ℝ) :
    gridFeature N (r*cos θ,r*sin θ) = r*angular N θ := by
  unfold gridFeature angular phi projection
  simp only [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cos_sub,mul_max_of_nonneg _ _ hr,mul_zero]
  congr 1; ring

private theorem radial (s : ℝ) :
    (∫ r in Ioi (0:ℝ), r*exp (-((1+s^2)/2)*r^2)) = 1/(1+s^2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=1) (b:=(1+s^2)/2)
    (by norm_num) (by norm_num) (by positivity)
  norm_num [Real.rpow_two, Real.Gamma_one] at h
  simp only [neg_mul, Real.rpow_neg_one] at *
  rw [h]; field_simp

private theorem polar_laplace (N : ℕ) (t : ℝ) :
    (∫ w, exp (-(t*gridFeature N w)^2/2) ∂standardPair) =
      (1/(2*π))*(∫ θ in Ioo (-π) π, 1/(1+(t*angular N θ)^2)) := by
  let f (p : ℝ×ℝ) := p.1*exp (-((1+(t*angular N p.2)^2)/2)*p.1^2)
  rw [standardPair_integral, ←integral_comp_polarCoord_symm]
  have eq : (∫ p in polarCoord.target, p.1 • ((gaussianPDFReal 0 1 (polarCoord.symm p).1 *
      gaussianPDFReal 0 1 (polarCoord.symm p).2)*exp (-(t*gridFeature N (polarCoord.symm p))^2/2))) =
      ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-π) π, (1/(2*π))*f p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r,θ⟩ ht
    change r*((gaussianPDFReal 0 1 (r*cos θ)*gaussianPDFReal 0 1 (r*sin θ))*
      exp (-(t*gridFeature N (r*cos θ,r*sin θ))^2/2)) = _
    rw [grid_polar N ht.1.le,gaussianPDFReal,gaussianPDFReal]
    simp only [NNReal.coe_one,mul_one,sub_zero,f]
    have hg := sq_sqrt (show 0 ≤ 2*π by positivity)
    rw [mul_mul_mul_comm (√(2*π))⁻¹ (exp _) (√(2*π))⁻¹ (exp _),←mul_inv,←sq,hg,
      ←Real.exp_add, mul_assoc _ (exp _) (exp _), ←Real.exp_add]
    have e : -(r*cos θ)^2/2 + (-(r*sin θ)^2/2 + -(t*(r*angular N θ))^2/2) =
        -((1+(t*angular N θ)^2)/2)*r^2 := by
      linear_combination -(r^2/2)*(sin_sq_add_cos_sq θ)
    rw [←add_assoc] at e
    rw [e]; ring
  have hr : IntegrableOn (fun r : ℝ => r*exp (-(1/2)*r^2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (s:=1) (by norm_num : 0<(1/2:ℝ)) (by norm_num)
  have ha : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (-π) π) := integrableOn_const (by simp)
  have hf : Integrable f ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) := by
    apply (hr.norm.mul_prod ha).mono'
    · have := angular_cont N; unfold f; fun_prop
    · apply ae_of_all; intro p
      simp only [f,Real.norm_eq_abs,abs_mul,abs_exp,mul_one]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ((t*angular N p.2)*p.1)]
  rw [eq,integral_const_mul,Measure.volume_eq_prod,←Measure.prod_restrict,integral_prod_symm f hf]
  simp only [f,radial]

private def phase (t x : ℝ) := Complex.exp (↑(t*x) * Complex.I)
private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by simp [phase,Complex.norm_exp]
private theorem gaussian_phase (s : ℝ) : (∫ a, phase s a ∂G) = (exp (-s^2/2):ℝ) := by
  have h := charFun_gaussianReal (μ:=0) (v:=1) s
  simp only [charFun_apply_real,Complex.ofReal_zero,mul_zero,zero_mul,NNReal.coe_one,
    Complex.ofReal_one,one_mul,zero_sub] at h
  simpa [phase,Complex.ofReal_exp,neg_div] using h

/-- Exact one-unit characteristic function after integrating both radial Gaussian variables. -/
theorem single_charFun (N : ℕ) (t : ℝ) :
    charFun (atomLaw.map (single N)) t =
      ((1/(2*π))*(∫ θ in Ioo (-π) π, 1/(1+(t*angular N θ)^2)) : ℝ) := by
  have hm : Measurable (single N) := by unfold single gridFeature phi projection; fun_prop
  rw [charFun_apply_real,integral_map hm.aemeasurable (by fun_prop)]
  simp only [←Complex.ofReal_mul]
  change (∫ z, phase t ((split z).1*gridFeature N (split z).2) ∂atomLaw) = _
  rw [split_preserving.integral_comp' (fun p : ℝ×(ℝ×ℝ) => phase t (p.1*gridFeature N p.2))]
  have hf : Integrable (fun p : ℝ×(ℝ×ℝ) => phase t (p.1*gridFeature N p.2)) (G.prod standardPair) := by
    apply (integrable_const (1:ℝ)).mono'
    · unfold phase gridFeature phi projection; fun_prop
    · exact ae_of_all _ (fun _ => (phase_norm _ _).le)
  rw [integral_prod_symm _ hf]
  simp_rw [show ∀ (w : ℝ×ℝ) (a : ℝ), phase t (a*gridFeature N w) = phase (t*gridFeature N w) a by
    intro w a; unfold phase; ring_nf,gaussian_phase]
  rw [integral_complex_ofReal,polar_laplace]

private theorem gridMean_eq_sum (N m : ℕ) (z : Seed m) :
    CircleScoreMargin.gridMean N m z = (1/√(m:ℝ))*∑ j : Fin m, single N ((currySeed m z) j) := by
  have he (i : Fin N) (j : Fin m) : CircleFlowPath.pre z j (CircleFlowPath.circleInput N i) =
      projection (physicalAngle i) (z (j,1),z (j,2)) := by
    simp only [CircleFlowPath.pre,CircleFlowPath.circleInput,CircleEscape.gridPoint,
      physicalAngle,projection]; ring
  have hc (j : Fin m) : (currySeed m z) j = fun k => z (j,k) := rfl
  unfold CircleScoreMargin.gridMean CircleFlowPath.output
  simp only [he,hc,single,gridFeature,phi,←Finset.mul_sum]
  simp_rw [←mul_div_assoc,Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- The exact characteristic function of the actual grid average at any finite width.
The factor at frequency `t / √m` is raised to the number of independent units. -/
theorem gridMean_charFun (N m : ℕ) (t : ℝ) :
    charFun ((seedLaw m).map (CircleScoreMargin.gridMean N m)) t =
      (((1/(2*π))*(∫ θ in Ioo (-π) π, 1/(1+((t/√(m:ℝ))*angular N θ)^2)) : ℝ):ℂ)^m := by
  let s := t/√(m:ℝ)
  let F (z : Atom) := phase s (single N z)
  have hm : Measurable (CircleScoreMargin.gridMean N m) := by
    unfold CircleScoreMargin.gridMean CircleFlowPath.output CircleFlowPath.pre; fun_prop
  rw [charFun_apply_real,integral_map hm.aemeasurable (by fun_prop)]
  have hp (z : Seed m) : Complex.exp (↑t * ↑(CircleScoreMargin.gridMean N m z) * Complex.I) =
      ∏ j, F ((currySeed m z) j) := by
    rw [gridMean_eq_sum]
    simp only [F,phase,Complex.ofReal_mul,Complex.ofReal_sum]
    rw [←Complex.exp_sum]
    congr 1
    simp only [s,Complex.ofReal_div,Complex.ofReal_one,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [hp]
  rw [(curry_preserving m).integral_comp' (fun h : Fin m → Atom => ∏ j, F (h j)),
    integral_fintype_prod_eq_pow,Fintype.card_fin]
  congr 1
  convert single_charFun N s using 1
  rw [charFun_apply_real,integral_map (by unfold single gridFeature phi projection; fun_prop) (by fun_prop)]
  simp [F,phase]

end CircleMajorityCF
