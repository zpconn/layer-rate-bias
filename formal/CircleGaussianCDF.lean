module
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! A uniform variance expansion of a centered Gaussian distribution function,
including mixtures with point mass at zero. -/
public section
noncomputable section
namespace CircleGaussianCDF
open scoped NNReal
open ProbabilityTheory MeasureTheory Real Set Filter Topology

def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)
def varianceCDF (s x : ℝ) : ℝ := (gaussianReal 0 s.toNNReal).real (Iic x)
def density (x : ℝ) : ℝ := (√(2*π))⁻¹*exp (-(x^2)/2)

private theorem density_eq : density=gaussianPDFReal 0 1 := by ext x; simp [density,gaussianPDFReal_def]

private theorem phi_integral (x : ℝ) : normalCDF x=∫ y in Iic x, density y := by
  unfold normalCDF Measure.real
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, density_eq, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic fun y _ => gaussianPDFReal_nonneg _ _ y

theorem normalCDF_deriv (x : ℝ) : HasDerivAt normalCDF (density x) x := by
  have hi : Integrable density := density_eq ▸ integrable_gaussianPDFReal 0 1
  have hc : Continuous density := by unfold density; fun_prop
  have hcf : normalCDF = fun z => (∫ y in (0:ℝ)..z, density y) + normalCDF 0 := by
    ext z
    rw [phi_integral,phi_integral,←intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
    ring
  rw [hcf]
  exact (intervalIntegral.integral_hasDerivAt_right hi.intervalIntegrable hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).add_const _

theorem density_bound (u : ℝ) : |density u| ≤ (√(2*π))⁻¹ := by
  rw [density,abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr (by nlinarith [sq_nonneg u]))

theorem normalCDF_lipschitz (x y : ℝ) : |normalCDF x-normalCDF y|≤ (√(2*π))⁻¹*|x-y| := by
  exact convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (normalCDF_deriv z).hasDerivWithinAt) (fun z _ => density_bound z) (Set.mem_univ y) (Set.mem_univ x)

theorem scale (s x : ℝ) (hs : 0<s) : varianceCDF s x =normalCDF (x/√s) := by
  have h := gaussianReal_map_const_mul (μ:=0) (v:=1) (√s)
  have hσ : (NNReal.mk ((√s)^2) (sq_nonneg _)) = s.toNNReal := by ext; simp [Real.sq_sqrt hs.le,hs.le]
  rw [hσ,mul_one,mul_zero] at h
  unfold varianceCDF normalCDF Measure.real
  rw [←h,Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext z
  change √s*z≤x ↔ z≤x/√s
  rw [le_div_iff₀ (sqrt_pos.mpr hs),mul_comm]

private theorem density_deriv (u : ℝ) : HasDerivAt density (-u*density u) u := by
  have h : HasDerivAt (fun x : ℝ => -(x^2)/2) (-u) u := by
    convert (((hasDerivAt_id u).pow 2).neg.div_const 2) using 1
    simp [id_eq];ring_nf;rfl
  have d := h.exp.const_mul ((√(2*π))⁻¹)
  change HasDerivAt density ((√(2*π))⁻¹*(exp (-(u^2)/2)* -u)) u at d
  convert d using 1
  unfold density;ring

private theorem weighted_bounds (u : ℝ) : |u| *|density u|≤1/2 ∧ |u| ^3*|density u|≤2 := by
  have hroot : 2≤√(2*π) := (le_sqrt (by norm_num) (by positivity)).mpr (by linarith [pi_gt_three])
  have hc : (√(2*π))⁻¹ ≤ 1/2 := (inv_le_comm₀ (by positivity) (by norm_num)).mpr (by simpa using hroot)
  let r := |u|
  have hr : 0≤r := abs_nonneg _
  have hr2 : r^2=u^2 := sq_abs _
  have hq : r≤1+r^2/4 := by nlinarith [sq_nonneg (r-2)]
  have he := Real.add_one_le_exp (r^2/4)
  have he' : r≤exp (r^2/2) := by nlinarith [Real.add_one_le_exp (r^2/2),sq_nonneg (r-1)]
  have hhh : r^2/4≤exp (r^2/4) := by linarith
  have hq2 : r≤exp (r^2/4) := by linarith
  have he3 : r^3≤4*exp (r^2/2) := by
    have hh := mul_le_mul hq2 hhh (by positivity) (exp_pos _).le
    rw [←exp_add,show r^2/4+r^2/4=r^2/2 by ring] at hh
    nlinarith only [hh]
  have hd : |density u|=(√(2*π))⁻¹ /exp (r^2/2) := by
    rw [density,abs_of_nonneg (by positivity),hr2,show -(u^2)/2= -(u^2/2) by ring,exp_neg]; rfl
  rw [hd]
  change r*(_ / _)≤_ ∧ r^3*(_ / _)≤_
  constructor
  · rw [←mul_div_assoc,div_le_iff₀ (exp_pos _)]
    nlinarith only [mul_le_mul he' hc (by positivity) (exp_pos _).le]
  · rw [←mul_div_assoc,div_le_iff₀ (exp_pos _)]
    nlinarith only [mul_le_mul he3 hc (by positivity) (by positivity)]

def slope (t : ℝ) : ℝ := -t*density t/2
private def u (t s : ℝ) := t/√s
private def smoothCDF (t s : ℝ) := normalCDF (u t s)
private def first (t s : ℝ) := -u t s*density (u t s)/(2*s)
private def second (t s : ℝ) := u t s*(3-(u t s)^2)*density (u t s)/(4*s^2)

private theorem argument_deriv (t : ℝ) {s : ℝ} (hs : 0<s) : HasDerivAt (u t) (-u t s/(2*s)) s := by
  have hr := sqrt_ne_zero'.mpr hs
  unfold u
  convert (hasDerivAt_const s t).div (hasDerivAt_sqrt hs.ne') hr using 1
  field_simp [hr,hs.ne']
  grind [Real.sq_sqrt hs.le]

private theorem first_deriv (t : ℝ) {s : ℝ} (hs : 0<s) : HasDerivAt (smoothCDF t) (first t s) s := by
  convert (normalCDF_deriv (u t s)).comp s (argument_deriv t hs) using 1
  · rfl
  · unfold first;ring

private theorem second_deriv (t : ℝ) {s : ℝ} (hs : 0<s) : HasDerivAt (first t) (second t s) s := by
  have hu := argument_deriv t hs
  have hd := (density_deriv (u t s)).comp s hu
  convert (hu.neg.mul hd).div ((hasDerivAt_id s).const_mul 2) (show 2*id s≠0 by simpa using mul_ne_zero (by norm_num : (2:ℝ)≠0) hs.ne') using 1
  · rfl
  · unfold second; simp only [id_eq,Pi.mul_apply,Pi.neg_apply,Function.comp_apply]; field_simp; ring

private theorem second_bound (t : ℝ) {s : ℝ} (hs : 1/2≤s) : |second t s|≤4 := by
  obtain ⟨h1,h3⟩ := weighted_bounds (u t s)
  let x := u t s
  have hj : |x*(3-x^2)*density x|≤ 3*(|x| *|density x|)+|x| ^3*|density x| := by
    rw [show x*(3-x^2)*density x=3*(x*density x)-x^3*density x by ring]
    calc
      _ ≤ |3*(x*density x)|+|x^3*density x| := abs_sub _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_mul,abs_pow]; norm_num
  unfold second
  rw [abs_div,abs_of_nonneg (show 0≤4*s^2 by positivity),div_le_iff₀ (show 0<4*s^2 by nlinarith [sq_nonneg (s-1/2)])]
  dsimp [x] at hj
  nlinarith [sq_nonneg (s-1/2)]

theorem tangent_remainder (t s : ℝ) (_hs : 0≤s) :
    |varianceCDF s t - normalCDF t - slope t*(s-1)|≤5*(s-1)^2 := by
  have hsl : |slope t|≤1/2 := by
    rw [slope,abs_div,abs_mul,abs_neg]; norm_num
    linarith [(weighted_bounds t).1]
  by_cases h : 1/2≤s
  · have hs' : 0<s := by linarith
    have hc (z : ℝ) (hz : z∈uIcc 1 s) : 1/2≤z :=
      (le_min (by norm_num) h).trans hz.1
    have hdiff (z : ℝ) (hz : z∈uIcc 1 s) :
        |first t z-first t 1| ≤ 4*|s-1| := by
      have hh := (convex_uIcc (1:ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy => (second_deriv t (by linarith [hc y hy])).hasDerivWithinAt)
        (fun y hy => second_bound t (hc y hy)) (left_mem_uIcc : (1:ℝ) ∈ uIcc 1 s) hz
      have hh' := Real.dist_le_of_mem_uIcc hz (left_mem_uIcc : (1:ℝ) ∈ uIcc 1 s)
      rw [Real.dist_eq,Real.dist_eq,abs_sub_comm 1 s] at hh'
      simp only [Real.norm_eq_abs] at hh
      exact hh.trans (by gcongr)
    let f := fun z => smoothCDF t z-first t 1*(z-1)
    have hf (z : ℝ) (hz : z∈uIcc 1 s) : HasDerivAt f (first t z-first t 1) z := by
      convert (first_deriv t (by linarith [hc z hz])).sub (((hasDerivAt_id z).sub_const 1).const_mul (first t 1)) using 1
      · rfl
      · ring
    have hh := (convex_uIcc (1:ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hf y hy).hasDerivWithinAt) hdiff (left_mem_uIcc : (1:ℝ) ∈ uIcc 1 s) (right_mem_uIcc : s ∈ uIcc 1 s)
    simp only [Real.norm_eq_abs,f,smoothCDF,first,u,sqrt_one,div_one,mul_one,sub_self,mul_zero,sub_zero] at hh
    rw [scale s t hs',slope]
    rw [show normalCDF (t/√s)-normalCDF t- -t*density t/2*(s-1)=
      normalCDF (t/√s)- -t*density t/2*(s-1)-normalCDF t by ring]
    refine hh.trans ?_
    nlinarith [sq_abs (s-1),sq_nonneg (s-1)]
  · have h1 : |varianceCDF s t-normalCDF t|≤1 := by
      unfold varianceCDF normalCDF
      apply abs_le.mpr
      exact ⟨by linarith [measureReal_nonneg (μ:=gaussianReal 0 s.toNNReal) (s:=Iic t),
        measureReal_le_one (μ:=gaussianReal 0 1) (s:=Iic t)],by
        linarith [measureReal_nonneg (μ:=gaussianReal 0 1) (s:=Iic t),
          measureReal_le_one (μ:=gaussianReal 0 s.toNNReal) (s:=Iic t)]⟩
    have hh := abs_sub (varianceCDF s t-normalCDF t) (slope t*(s-1))
    rw [abs_mul,abs_of_nonpos (by linarith : s-1≤0)] at hh
    nlinarith [mul_le_mul_of_nonneg_right hsl (by linarith : 0≤ -(s-1)),sq_nonneg (s-1/2)]
theorem varianceCDF_measurable (t : ℝ) : Measurable (fun s => varianceCDF s t) := by
  have hm : Measurable normalCDF := (continuous_iff_continuousAt.mpr
    (fun x => (normalCDF_deriv x).continuousAt)).measurable
  have he : (fun s => varianceCDF s t) =
      (Set.Ioi (0:ℝ)).piecewise (fun s => normalCDF (t/√s)) (fun _ => varianceCDF 0 t) := by
    ext s
    by_cases h : 0<s
    · simp [Set.piecewise, h, scale s t h]
    · simp [Set.piecewise, h, varianceCDF, Real.toNNReal_of_nonpos (le_of_not_gt h)]
  rw [he]
  exact Measurable.piecewise measurableSet_Ioi (hm.comp (by fun_prop)) measurable_const

theorem rescale (s t v : ℝ) (hs : 0≤s) (hv : 0<v) :
    varianceCDF s (t*√v)=varianceCDF (s/v) t := by
  rcases hs.eq_or_lt with h|h
  · subst s
    simp only [zero_div,varianceCDF,Real.toNNReal_zero,gaussianReal_zero_var,Measure.real]
    rw [Measure.dirac_apply' _ measurableSet_Iic,Measure.dirac_apply' _ measurableSet_Iic]
    simp [Set.indicator_apply,mul_nonneg_iff_of_pos_right (sqrt_pos.mpr hv)]
  · rw [scale s _ h,scale _ _ (div_pos h hv),Real.sqrt_div hs]
    congr 1
    field_simp [sqrt_ne_zero'.mpr h,sqrt_ne_zero'.mpr hv]

end CircleGaussianCDF
